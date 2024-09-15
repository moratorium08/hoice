//! Overall Design of AbsADT
//!
//! ## Data Structure
//!
//! - Enc: enc
//!   - The encoding is a map from ADT terms to integer expressions.
//! - Model: model
//!   - A model of SMT modulo ADT
//!
//! ## Main Algorithm
//! 1. Solve the CHC over LIA using Spacer with the current approximation `enc`.
//!   - If sat, then the original problem is also sat, and the algorithm
//!     terminates.
//! 2. From the counterexample, extract a non-recursive counterexample C (SMT
//! constraints over ADT but not with RDF) for the original CHC, and add to
//! cexs: Vec<Constraint>.
//!   - This forms an underapproximation original CHC.
//!   - If C is sat → the original problem is unsatisfiable.
//! 3. Apply the current encode to the extracted constraints and obtain the
//! resulting counterexample model (over ADT) by a SMT solver. Then add to
//! pseudo_cexs: Vec<Model>.
//! 4. Generate a new approximation enc’ that can refute all cexs: (GenEnc).
//!   - If C is sat with enc’, go back to step 2.
//!   - If C is unsat with enc’, update enc to enc’ and return to step 1.
//!
//! ## GenEnc
//!
//! - Input: pseudo_cexs
//! - Output: new encoding enc’
//!
//! ### Algorithm:
//!
//! 1. Find a good abstraction from a set of templates
//! 2. TBD
//!
//!
//! ## Some Assumptions
//! - set of ADT does not change from start to end during `work`
//!   - they are defined as the global hashconsed objects
use chc::{AbsInstance, CEX};
use enc::Encoder;
use hyper_res::ResolutionProof;

use crate::common::{smt::FullParser as Parser, *};
use crate::info::{Pred, VarInfo};

use crate::common::*;
use crate::term::Term;
use crate::unsat_core::UnsatRes;
use std::path::PathBuf;

mod chc;
mod enc;
mod hyper_res;
mod learn;
mod spacer;

/// To be removed. Just for checking some behaviors
fn playground(instance: &Arc<Instance>) {
    // ~~~playground~~~
    let decs = dtyp::get_all();
    assert!(!decs.is_empty(), "no ADT is defined");

    for (name, dtyp) in decs.iter() {
        println!("dtype name: {}\n{:#?}", name, dtyp);
    }

    let ty = dtyp::of_constructor("nil").unwrap();
    println!("ty: {}", ty.name);
    let idx = dtyp::TPrmIdx::from(0);
    let ty = &ty.prms[idx];
    println!("ty: {}", ty);
    for c in instance.clauses().into_iter() {
        println!("clause: {:#?}", c.vars);
    }
}

pub struct AbsConf<'original> {
    pub cexs: Vec<chc::CEX>,
    pub instance: AbsInstance<'original>,
    pub solver: Solver<Parser>,
    pub encs: BTreeMap<Typ, Encoder>,
    epoch: usize,
}

fn initialize_dtyp(v: VarInfo, encs: &mut BTreeMap<Typ, Encoder>) -> Res<()> {
    let (ty, _) = v.typ.dtyp_inspect().unwrap();
    let mut approxs = BTreeMap::new();
    for (constr_name, sels) in ty.news.iter() {
        let mut args = VarInfos::new();

        for (sel, _) in sels.iter() {
            let info = VarInfo::new(sel, typ::int(), args.next_index());
            args.push(info);
        }
        let terms = vec![term::int_zero()];
        let approx = enc::Approx { args, terms };
        approxs.insert(constr_name.to_string(), approx);
    }
    let typ = v.typ.clone();
    let n_params = 1;
    let enc = enc::Enc {
        typ,
        n_params,
        approxs,
    };
    let r = encs.insert(v.typ, enc);
    debug_assert!(r.is_none());
    Ok(())
}

impl<'original> AbsConf<'original> {
    fn new(original: &'original Instance) -> Res<Self> {
        let instance = AbsInstance::new(original)?;
        let cexs = Vec::new();
        let solver = conf.solver.spawn("absadt", Parser, original)?;
        let encs = BTreeMap::new();

        Ok(AbsConf {
            instance,
            cexs,
            solver,
            encs,
            epoch: 0,
        })
    }

    /// To be removed.
    fn playground(&mut self) -> Res<()> {
        println!("playground");
        let list = dtyp::get("Lst2").unwrap();
        let slcs = list.selectors_of("cons2").unwrap();

        println!("selectors:");
        for (s, t) in slcs {
            println!("{}: {}", s, t);
        }
        let mut file = self.instance.instance_log_files("hoge")?;
        let last = &self.instance.clauses[0];
        let ty = last
            .vars
            .iter()
            .find_map(|x| if x.typ.is_dtyp() { Some(&x.typ) } else { None })
            .unwrap()
            .clone();
        self.encs.insert(ty.clone(), Encoder::len_ilist(ty));

        //self.instance.dump_as_smt2(&mut file, "before", false)?;
        //let encoded = self.encode();
        //encoded.dump_as_smt2(&mut file, "after", false)?;

        //encoded.dump_as_smt2(&mut file, "w/ tag", true)?;

        //match encoded.check_sat() {
        //    Ok(either::Left(())) => {
        //        println!("sat: {:#?}", ());
        //    }
        //    Ok(either::Right(x)) => {
        //        println!("unsat: {x}");
        //        let cex = self.instance.get_cex(&x);
        //        println!("cex: {cex}");
        //    }
        //    Err(e) => {
        //        println!("error: {:#?}", e);
        //    }
        //}

        //chc::test_check_sat();
        Ok(())
    }

    fn initialize_encs(&mut self) -> Res<()> {
        let encs = &mut self.encs;
        let instance = &self.instance;
        for c in instance.clauses.iter() {
            for v in c.vars.iter() {
                if v.typ.is_dtyp() && !encs.contains_key(&v.typ) {
                    initialize_dtyp(v.clone(), encs)?;
                }
            }
        }
        Ok(())
    }

    fn log_epoch(&self, e: &AbsInstance) -> Res<()> {
        let mut encoder_s = "[encoders]\n".to_string();
        for (tag, e) in self.encs.iter() {
            encoder_s += &format!("[{}]", tag);
            encoder_s += &e.to_string();
        }
        let mut file = self
            .instance
            .instance_log_files(format!("encoded-epoch-{}", self.epoch))?;
        e.dump_as_smt2(&mut file, &encoder_s, false)?;
        Ok(())
    }

    fn run(&mut self) -> Res<either::Either<(), ()>> {
        //self.playground()?;
        self.initialize_encs()?;
        let r = loop {
            self.epoch += 1;
            let encoded = self.encode();
            self.log_epoch(&encoded)?;
            match encoded.check_sat()? {
                either::Left(()) => {
                    break either::Left(());
                }
                either::Right(x) => {
                    let cex = self.instance.get_cex(&x);
                    log_debug!("cex: {}", cex);
                    learn::work(&mut self.encs, &cex, &mut self.solver)?;
                }
            }
        };
        Ok(r)
    }
}

impl<'a> AbsConf<'a> {
    pub fn encode_clause(&self, c: &chc::AbsClause) -> chc::AbsClause {
        let ctx = enc::EncodeCtx::new(&self.encs);
        let (new_vars, introduced) = enc::tr_varinfos(&self.encs, &c.vars);
        let encode_var = |typ: &Typ, var| {
            if let Some(x) = introduced.get(var) {
                let mut res = Vec::new();
                for y in x.iter() {
                    res.push(term::var(*y.idx, y.typ.clone()));
                }
                res
            } else {
                vec![term::var(*var, typ.clone())]
            }
        };
        let r = ctx.encode(&c.lhs_term, &encode_var);
        let lhs_term = term::and(r);
        let mut lhs_preds = Vec::with_capacity(c.lhs_preds.len());
        for lhs_app in c.lhs_preds.iter() {
            let mut new_args = VarMap::new();
            for arg in lhs_app.args.iter() {
                for encoded in ctx.encode(arg, &encode_var) {
                    new_args.push(encoded);
                }
            }
            lhs_preds.push(chc::PredApp {
                pred: lhs_app.pred,
                args: new_args.into(),
            });
        }
        let rhs = c.rhs.as_ref().map(|(pred, args)| {
            let mut new_args = Vec::new();
            for arg in args.iter() {
                if let Some(approx) = introduced.get(arg) {
                    for approx_arg in approx.iter() {
                        new_args.push(approx_arg.idx);
                    }
                } else {
                    new_args.push(arg.clone());
                }
            }
            (*pred, new_args)
        });
        let res = chc::AbsClause {
            vars: new_vars,
            lhs_term,
            lhs_preds,
            rhs,
        };
        res
    }
    fn encode_sig(&self, sig: &VarMap<Typ>) -> VarMap<Typ> {
        let mut new_sig = VarMap::new();
        for ty in sig.iter() {
            if let Some(enc) = self.encs.get(&ty) {
                enc.push_approx_typs(&mut new_sig)
            } else {
                new_sig.push(ty.clone());
            }
        }
        new_sig
    }

    fn encode_pred(&self, p: &Pred) -> Pred {
        let mut pred = p.clone();
        pred.sig = self.encode_sig(&pred.sig);
        pred
    }
    pub fn encode(&self) -> chc::AbsInstance {
        let clauses = self
            .instance
            .clauses
            .iter()
            .map(|c| self.encode_clause(c))
            .collect();
        let preds = self
            .instance
            .preds
            .iter()
            .map(|p| self.encode_pred(p))
            .collect();
        self.instance.clone_with_clauses(clauses, preds)
    }
}

/// Abstract ADT terms with integer expressions, and solve the instance by an external solver.
///
/// Returns
///
/// - a model if the instance is sat,
/// - `None` if not in `infer` mode,
/// - an [`UnsatRes`] if unsat.
///
/// Assumes the instance is **already pre-processed**.
///
/// [`UnsatRes`]: ../unsat_core/enum.UnsatRes.html (UnsatRes struct)
pub fn work(
    instance: &Arc<Instance>,
    _profiler: &Profiler,
) -> Res<Option<Either<ConjCandidates, UnsatRes>>> {
    log_info!("ABS ADT is enabled");
    //playground(instance);

    let mut absconf = AbsConf::new(instance)?;
    let r = match absconf.run()? {
        either::Left(()) => either::Left(ConjCandidates::new()),
        either::Right(_) => either::Right(UnsatRes::None),
    };
    Ok(Some(r))
}
