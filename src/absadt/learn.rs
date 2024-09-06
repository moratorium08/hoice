use super::chc::CEX;
use super::enc::*;
use crate::common::{smt::FullParser as Parser, Cex as Model, *};
use crate::info::VarInfo;

pub struct LearnCtx<'a> {
    encs: &'a mut BTreeMap<Typ, Enc>,
    cex: &'a CEX,
    solver: &'a mut Solver<Parser>,
    models: Vec<Model>,
}

trait Template {
    fn encode_term(&self, term: &Term) -> Term;
    fn update(&self, encs: &mut BTreeMap<Typ, Enc>, model: &Model) -> Res<()>;
}

struct LinearApprox {
    // n_args * num of its approx
    coef: VarMap<VarMap<VarIdx>>,
    cnst: VarIdx,
}

impl LinearApprox {
    fn new(coef: VarMap<VarMap<VarIdx>>, fvs: &mut VarInfos) -> Self {
        let idx = fvs.next_index();
        let info = VarInfo::new("const_value".to_string(), typ::int(), idx);
        fvs.push(info);
        Self { coef, cnst: idx }
    }
    fn apply(&self, argss: impl IntoIterator<Item = Vec<Term>>) -> Term {
        let mut res = vec![term::var(self.cnst, typ::int())];
        for (args, coefs) in argss.into_iter().zip(self.coef.iter()) {
            assert_eq!(args.len(), coefs.len());
            for (arg, coef) in args.iter().zip(coefs.iter()) {
                let t = term::mul(vec![term::var(*coef, typ::int()), arg.clone()]);
                res.push(t);
            }
        }
        term::add(res)
    }
}

#[test]
fn test_linear_approx_apply() {
    let mut fvs = VarInfos::new();
    // dtyp = Cons(x)
    let coef = LinearTemplate::prepare_coefs("dtyp-cons", &mut fvs, 1);
    let approx = LinearApprox::new(vec![coef].into(), &mut fvs);

    let x = term::val(val::int(4));
    let argss = vec![vec![x.clone()]];
    let t = approx.apply(argss.into_iter());

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
struct LinearTemplate<'a> {
    target_enc: &'a Enc, // Data type to be abstracted
    n_params: usize,
    approx_template: BTreeMap<String, LinearApprox>,
}

impl<'a> LinearTemplate<'a> {
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
    fn new(target_enc: &'a Enc, fvs: &mut VarInfos, encs: &'a BTreeMap<Typ, Enc>) -> Self {
        let typ = &target_enc.typ;
        let n_params = target_enc.n_params + 1;
        let mut approx_template = BTreeMap::new();

        // prepare LinearApprox for each constructor
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
                // prepare coefs for constr.sel, which involes generating new template variables to be manged
                // at the top level (`fvs`)
                let args = LinearTemplate::prepare_coefs(name, fvs, n);
                coefs.push(args);
            }

            approx_template.insert(constr.to_string(), LinearApprox::new(coefs.into(), fvs));
        }

        Self {
            target_enc,
            n_params,
            approx_template,
        }
    }
}

//fn get_n_args(enc: &Enc, key: &str) -> usize {
//    let approx = enc.approxs.get(key).unwrap();
//    let (dtyp, prms) = enc.typ.dtyp_inspect().unwrap();
//
//    dtyp.news.get(&key).unwrap();
//}

impl<'a> Template for LinearTemplate<'a> {
    fn encode_term(&self, term: &Term) -> Term {
        unimplemented!();
    }

    fn update(&self, encs: &mut BTreeMap<Typ, Enc>, model: &Cex) -> Res<()> {
        todo!()
    }
}

//fn get_templates(n_arg: usize) -> Vec<Box<dyn Template>> {
//    vec![Box::new(LinearTemplate::new(n_arg))]
//}

impl<'a> LearnCtx<'a> {
    pub fn new(
        encs: &'a mut BTreeMap<Typ, Enc>,
        cex: &'a CEX,
        solver: &'a mut Solver<Parser>,
    ) -> Self {
        let models = Vec::new();
        LearnCtx {
            encs,
            cex,
            solver,
            models,
        }
    }

    /// Define encoding functions
    ///
    /// Assumption: Data types are all defined.
    fn define_enc_funs(&mut self) -> Res<()> {
        let ctx = super::enc::EncodeCtx::new(&self.encs);
        let mut funs = Vec::new();
        for enc in self.encs.values() {
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
        self.cex.define_assert(&mut self.solver, &self.encs)?;
        let b = self.solver.check_sat()?;
        if !b {
            return Ok(None);
        }
        let model = self.solver.get_model()?;
        let model = Parser.fix_model(model)?;
        let cex = Model::of_model(&self.cex.vars, model, true)?;
        Ok(Some(cex))
    }

    fn instantiate_template(&mut self, templates: Vec<Box<dyn Template>>) -> Res<()> {
        self.solver.reset()?;
        //let cex_instantiated = self.cex.term.subst_total()
        Ok(())
    }

    fn apply_template(&self, v: &Val, templates: &BTreeMap<Typ, LinearTemplate>) -> Vec<Term> {
        let ty = v.typ();
        match templates.get(&ty) {
            Some(tpl) => {
                let (vty, tag, args) = v.dtyp_inspect().unwrap();
                debug_assert_eq!(&ty, vty);

                let mut arg_values = Vec::new();
                for arg in args {
                    let v = self.apply_template(arg, templates);
                    arg_values.push(v);
                }

                // 1. use the existing encoders
                let approx = self.encs.get(&ty).unwrap().approxs.get(tag).unwrap();
                // TODO: append another argument to the existing approxs
                let mut terms = approx.apply(arg_values.clone().into_iter().flatten().collect());
                // 2. use the template encoder
                let tpl_approx = tpl.approx_template.get(tag).unwrap();
                let term = tpl_approx.apply(arg_values.into_iter());
                terms.push(term);

                terms
            }
            None => vec![term::val(v.clone())],
        }
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

        let mut fvs = VarInfos::new();
        let mut templates = BTreeMap::new();
        for (k, e) in self.encs.iter() {
            let enc = LinearTemplate::new(e, &mut fvs, &self.encs);
            templates.insert(k.clone(), enc);
        }
        //let mut form = Vec::new();
        for m in self.models.iter() {
            //let mut substs = VarHMap::new();
            for var in self.cex.vars.iter() {
                let v = &m[var.idx];
                todo!("use enc::encode?");
                //let vs = self.apply_template(v, &templates);
                //substs.insert(var.idx, term::val(v));
            }
            //let r = self.cex.term.subst_total(&substs);
            //form.push(r);
        }

        //
        unimplemented!()
    }

    pub fn work(&mut self) -> Res<()> {
        // We now only consider the linear models
        // Appendinx them to the existing encodings
        let mut models = Vec::new();
        loop {
            // 1. Check if the new encoding can refute the counterexample
            match self.get_model()? {
                // The current cex is refuted
                None => {
                    break;
                }
                Some(model) => {
                    println!("model: {}", model);
                    models.push(model);
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
    encs: &'a mut BTreeMap<Typ, Enc>,
    cex: &'a CEX,
    solver: &mut Solver<Parser>,
) -> Res<()> {
    let mut learn_ctx = LearnCtx::new(encs, cex, solver);
    learn_ctx.work()?;
    Ok(())
}
