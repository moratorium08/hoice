use super::chc::CEX;
use super::enc::*;
use crate::common::{smt::FullParser as Parser, Cex as Model, *};
use crate::info::VarInfo;

pub struct LearnCtx<'a> {
    encs: BTreeMap<Typ, Enc<LinearApprox>>,
    original_encs: &'a BTreeMap<Typ, Encoder>,
    cex: &'a CEX,
    solver: &'a mut Solver<Parser>,
    models: Vec<Model>,
}

struct LinearApprox {
    /// Existing approx
    approx: Approx,
    // approx template
    // n_args * num of its approx
    coef: VarMap<VarMap<VarIdx>>,
    cnst: VarIdx,
}

impl Approximation for LinearApprox {
    fn apply(&self, arg_terms: &[Term]) -> Vec<Term> {
        let mut terms = self.approx.apply(arg_terms);
        let mut res = vec![term::var(self.cnst, typ::int())];
        let coefs = self.coef.iter().flatten();
        for (arg, coef) in arg_terms.into_iter().zip(coefs) {
            let t = term::mul(vec![term::var(*coef, typ::int()), arg.clone()]);
            res.push(t);
        }
        terms.push(term::add(res));
        terms
    }
}

impl LinearApprox {
    fn new(coef: VarMap<VarMap<VarIdx>>, fvs: &mut VarInfos, approx: Approx) -> Self {
        let idx = fvs.next_index();
        let info = VarInfo::new("const_value".to_string(), typ::int(), idx);
        fvs.push(info);
        Self {
            coef,
            cnst: idx,
            approx,
        }
    }
}

#[test]
fn test_linear_approx_apply() {
    let mut fvs = VarInfos::new();
    // dtyp = Cons(x)
    let coef = prepare_coefs("dtyp-cons", &mut fvs, 1);
    let approx = LinearApprox::new(vec![coef].into(), &mut fvs, Approx::empty());

    let x = term::val(val::int(4));
    let argss = vec![x.clone()];
    let mut t = approx.apply(&argss);

    assert_eq!(t.len(), 1);
    let t = t.remove(0);

    let t2 = term::add(vec![
        term::var(1, typ::int()),
        term::mul(vec![term::var(0, typ::int()), x.clone()]),
    ]);
    println!("t: {}", t);
    println!("t2: {}", t2);
    for (a, b) in [(4i64, 3i64), (1, 2), (-4, 0)].into_iter() {
        let subst: VarHMap<_> = (0..2)
            .map(|x| VarIdx::from(x))
            .zip(vec![term::val(val::int(a)), term::val(val::int(b))].into_iter())
            .collect();
        assert_eq!(
            t.subst_total(&subst).unwrap().0.as_val(),
            t2.subst_total(&subst).unwrap().0.as_val()
        );
    }
}

fn prepare_coefs<S>(varname: S, fvs: &mut VarInfos, n: usize) -> VarMap<VarIdx>
where
    S: AsRef<str>,
{
    let varname = varname.as_ref();
    let mut res = VarMap::new();
    for i in 0..n {
        let idx = fvs.next_index();
        let info = VarInfo::new(format!("{varname}-{i}"), typ::int(), idx);
        res.push(idx);
        fvs.push(info);
    }
    res
}

impl<'a> LearnCtx<'a> {
    pub fn new(
        encs: &'a mut BTreeMap<Typ, Encoder>,
        cex: &'a CEX,
        solver: &'a mut Solver<Parser>,
    ) -> Self {
        let models = Vec::new();
        let mut fvs = VarInfos::new();

        let mut new_encs = BTreeMap::new();

        // prepare LinearApprox for each constructor
        for (typ, enc) in encs.iter() {
            let mut approxs = BTreeMap::new();
            for constr in typ.dtyp_inspect().unwrap().0.news.keys() {
                let (ty, prms) = typ.dtyp_inspect().unwrap();
                let mut coefs = VarMap::new();
                // each constructor has a set of selectors
                for (sel, ty) in ty.selectors_of(constr).unwrap().iter() {
                    let ty = ty.to_type(Some(prms)).unwrap();
                    let n = match encs.get(&ty) {
                        Some(enc_for_ty) => {
                            // prepare template coefficients for all the approximations of the argument
                            enc_for_ty.n_params + 1
                        }
                        None => {
                            assert!(ty.is_int());
                            1
                        }
                    };
                    let name = format!("{constr}-{sel}");
                    // prepare coefs for constr-sel, which involes generating new template variables manged
                    // at the top level (`fvs`)
                    let args = prepare_coefs(name, &mut fvs, n);
                    coefs.push(args);
                }

                let mut approx = enc.approxs.get(constr).unwrap().clone();
                let n_args: usize = coefs
                    .iter()
                    .map(|x| x.iter().map(|_| 1).sum::<usize>())
                    .sum();
                // insert dummy variables for newly-introduced approximated integers
                for _ in 0..(n_args - approx.args.len()) {
                    approx
                        .args
                        .push(VarInfo::new("tmp", typ::int(), approx.args.next_index()));
                }
                approxs.insert(
                    constr.to_string(),
                    LinearApprox::new(coefs.into(), &mut fvs, approx),
                );
            }
            let enc = Enc {
                approxs,
                typ: typ.clone(),
                n_params: enc.n_params + 1,
            };
            new_encs.insert(typ.clone(), enc);
        }

        LearnCtx {
            encs: new_encs,
            original_encs: encs,
            cex,
            solver,
            models,
        }
    }

    /// Define encoding functions
    ///
    /// Assumption: Data types are all defined.
    fn define_enc_funs(&mut self) -> Res<()> {
        let ctx = super::enc::EncodeCtx::new(&self.original_encs);
        let mut funs = Vec::new();
        for enc in self.original_encs.values() {
            enc.generate_enc_fun(&ctx, &mut funs)?;
        }

        let funs_strs = funs.into_iter().map(|(funname, ty, term)| {
            let args = vec![("v_0", ty.to_string())];
            let body = term.to_string();
            (funname, args, "Int", body)
        });
        self.solver.define_funs_rec(funs_strs)?;
        Ok(())
    }

    /// Define data types
    fn define_datatypes(&mut self) -> Res<()> {
        dtyp::write_all(&mut self.solver, "")?;
        Ok(())
    }

    fn get_model(&mut self) -> Res<Option<Model>> {
        self.solver.reset()?;
        self.define_datatypes()?;
        self.define_enc_funs()?;
        self.cex
            .define_assert(&mut self.solver, &self.original_encs)?;
        let b = self.solver.check_sat()?;
        if !b {
            return Ok(None);
        }
        let model = self.solver.get_model()?;
        let model = Parser.fix_model(model)?;
        let cex = Model::of_model(&self.cex.vars, model, true)?;
        Ok(Some(cex))
    }
    fn get_instantiation(&self) -> Res<Option<Model>> {
        // 1. Let l1, ..., lk be li in fv(cex)
        // 2. vis = [[m[li] for m in self.models] for li in l1, ..., lk]
        // 4. Declare a1, ... ak in coef(enc) as free variables
        // 5. Declare template functions for each dtype <- not needed?
        // form <- T
        // 6. for vi in vis:
        //    r <- cex
        //    for li in l1, ..., lk:
        //       r <- r.subst(li, enc.encode(vi))
        //    form <- form /\ r
        // 7. solve form and return the model for
        // return form

        // templates encoder
        let mut form = Vec::new();
        let encoder = EncodeCtx::new(&self.encs);
        for m in self.models.iter() {
            println!("models:");
            for (i, v) in m.iter().enumerate() {
                println!("- v_{i}: {}", v);
            }
            //let mut substs = VarHMap::new();
            let mut terms = encoder.encode(&self.cex.term, &|_: &Typ, v: &VarIdx| {
                let v = &m[*v];
                println!("v: {}", v);
                let terms = encoder.encode_val(v);
                for t in terms.iter() {
                    println!("- {t}");
                }
                terms
            });
            println!("encoded");
            form.append(&mut terms)
        }
        // solve the form
        println!("forms");
        for f in form.iter() {
            println!("- {}", f);
        }
        let form = term::and(form);
        println!("form: {}", form);
        unimplemented!()
    }

    pub fn work(&mut self) -> Res<()> {
        // We now only consider the linear models
        // Appendinx them to the existing encodings
        loop {
            // 1. Check if the new encoding can refute the counterexample
            match self.get_model()? {
                // The current cex is refuted
                None => {
                    break;
                }
                Some(model) => {
                    println!("model: {}", model);
                    self.models.push(model);
                }
            }
            // 2. If not, learn something new
            match self.get_instantiation()? {
                None => panic!("Linear Template is not enough"),
                Some(model) => {
                    //enc.update(self.encs, &model);
                }
            }
        }
        Ok(())
    }
}

/// Entrypoint for the learning algorithm
///
/// If this function returns Ok(()), some encodings are appended to `encs`
/// so that `cex` can be refuted.
pub fn work<'a>(
    encs: &'a mut BTreeMap<Typ, Encoder>,
    cex: &'a CEX,
    solver: &mut Solver<Parser>,
) -> Res<()> {
    let mut learn_ctx = LearnCtx::new(encs, cex, solver);
    learn_ctx.work()?;
    Ok(())
}
