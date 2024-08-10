use crate::common::*;
use crate::info::{Pred, VarInfo};

use super::chc::AbsInstance;

pub struct Approx {
    /// Definition of the arguments
    pub args: VarInfos,
    /// n terms for approximation
    pub terms: Vec<Term>,
}

impl Approx {
    pub fn apply(&self, arg_terms: Vec<Term>) -> Vec<Term> {
        let mut res = Vec::with_capacity(self.terms.len());
        for term in self.terms.iter() {
            let subst_map: VarHMap<_> = self
                .args
                .iter()
                .map(|x| x.idx)
                .zip(arg_terms.iter().cloned())
                .collect();
            res.push(term.subst_total(&subst_map).unwrap().0);
        }
        res
    }
}

/// Enc is an encoding of ADT terms to integer expressions.
///
/// Assumption: typ is a monomorphic type.
pub struct Enc {
    /// Number of parameters for approximation
    pub typ: Typ,
    pub n_params: usize,
    pub approxs: BTreeMap<String, Approx>,
}

impl Enc {
    fn gen_typ(&self, varmap: &mut VarInfos, orig_name: &str) -> VarMap<VarInfo> {
        let mut introduced = VarMap::new();
        for i in 0..self.n_params {
            let new_var_idx = varmap.next_index();
            let var_name = format!("{}_{}", orig_name, i);
            let new_var = VarInfo::new(var_name, typ::int(), new_var_idx);
            varmap.push(new_var.clone());
            introduced.push(new_var);
        }
        introduced
    }
}

pub struct EncodeCtx<'a> {
    instance: &'a super::chc::AbsInstance<'a>,
    introduced: VarHMap<VarMap<VarInfo>>,
}

impl<'a> EncodeCtx<'a> {
    fn tr_varinfos(&self, varmap: &VarInfos) -> (VarInfos, VarHMap<VarMap<VarInfo>>) {
        let mut new_varmap = VarInfos::new();
        let mut orig2approx_var = VarHMap::new();
        for v in varmap.iter() {
            if let Some(enc) = self.instance.encs.get(&v.typ) {
                let introduced = enc.gen_typ(&mut new_varmap, &v.name);
                orig2approx_var.insert(v.idx, introduced);
            } else {
                // base types (not approximated)
                new_varmap.push(v.clone());
            }
        }
        (new_varmap, orig2approx_var)
    }
    pub fn new(instance: &'a super::chc::AbsInstance<'a>) -> Self {
        Self {
            instance,
            introduced: VarHMap::new(),
        }
    }
    fn wrap(&self, term: &Term) -> Term {
        unimplemented!()
    }
    fn encode_val(&self, val: &Val) -> Vec<Term> {
        unimplemented!()
    }
    // fn handle_dtype_app(&self, dtyp: &DTyp, op: &Op, argss: Vec<Vec<Term>>) -> Vec<Term> {
    //     match op {
    //         Op::Eql => {
    //
    //         }
    //         Op::Ite => todo!(),
    //         Op::Add
    //         | Op::Sub
    //         | Op::Mul
    //         | Op::CMul
    //         | Op::IDiv
    //         | Op::Div
    //         | Op::Rem
    //         | Op::Mod
    //         | Op::Gt
    //         | Op::Ge
    //         | Op::Le
    //         | Op::Lt
    //         | Op::Impl
    //         | Op::Not
    //         | Op::And
    //         | Op::Or
    //         | Op::Distinct
    //         | Op::ToInt
    //         | Op::ToReal
    //         | Op::Store
    //         | Op::Select => panic!("invalid operator for ADT: {}", op),
    //     }
    // }
    fn handle_app(
        &self,
        typ: &Typ,
        op: &Op,
        args: impl IntoIterator<Item = &'a Term>,
    ) -> Vec<Term> {
        let argss = args
            .into_iter()
            .map(|arg| self.encode(arg))
            .collect::<Vec<_>>();
        if argss.len() == 0 {
            return vec![term::app(op.clone(), Vec::new())];
        }
        match typ.get() {
            typ::RTyp::Unk
            | typ::RTyp::Int
            | typ::RTyp::Real
            | typ::RTyp::Bool
            | typ::RTyp::Array { .. }
            | typ::RTyp::DTyp { .. } => {
                let l = argss[0].len();
                let mut res = Vec::with_capacity(l);
                for i in 0..l {
                    let mut new_args = Vec::with_capacity(argss.len());
                    for args in argss.iter() {
                        debug_assert!(args.len() == l);
                        new_args.push(args[i].clone());
                    }
                    res.push(term::app(op.clone(), new_args));
                }
                res
            } //typ::RTyp::DTyp { dtyp, prms } => self.handle_dtype_app(dtyp, op, argss),
        }
    }
    fn handle_dtypnew(&self, typ: &Typ, name: &str, argss: Vec<Vec<Term>>) -> Vec<Term> {
        let enc = if let Some(enc) = self.instance.encs.get(typ) {
            enc
        } else {
            let mut res = Vec::new();
            for args in argss.iter() {
                res.push(term::dtyp_new(typ.clone(), name.to_string(), args.clone()));
            }
            return res;
        };
        let approx = enc.approxs.get(name).unwrap();
        let args = argss.into_iter().flatten().collect();
        approx.apply(args)
    }
    fn handle_dtypslc(&self, typ: &Typ, name: &str, argss: &Vec<Vec<Term>>) -> Vec<Term> {
        unimplemented!()
    }
    fn handle_dtyptst(&self, typ: &Typ, name: &str, argss: &Vec<Vec<Term>>) -> Vec<Term> {
        unimplemented!()
    }
    pub fn encode(&self, term: &Term) -> Vec<Term> {
        match term.get() {
            RTerm::Var(x, y) => {
                if let Some(x) = self.introduced.get(y) {
                    let mut res = Vec::new();
                    for y in x.iter() {
                        res.push(term::var(*y.idx, y.typ.clone()));
                    }
                    res
                } else {
                    vec![term.clone()]
                }
            }
            RTerm::Cst(val) => self.encode_val(val),
            RTerm::App { typ, op, args, .. } => self.handle_app(typ, op, args),
            RTerm::DTypNew {
                typ, name, args, ..
            } => {
                let argss = args.iter().map(|arg| self.encode(arg)).collect::<Vec<_>>();
                self.handle_dtypnew(typ, name, argss)
            }
            RTerm::DTypSlc {
                typ, name, term, ..
            } => {
                unimplemented!()
            }
            RTerm::DTypTst {
                typ, name, term, ..
            } => {
                unimplemented!()
            }
            RTerm::CArray { term: t, typ, .. } => {
                let terms = self.encode(t);
                let mut res = Vec::with_capacity(terms.len());
                for t in terms {
                    res.push(term::cst_array(typ.clone(), t));
                }
                res
            }
            RTerm::Fun {
                ..
                //depth,
                //typ,
                //name,
                //args,
            } => {
                // how do I handle the function whose return type is a datatype?
                //let argss = args.iter().map(|arg| self.encode(arg)).collect::<Vec<_>>();
                //let args = argss.into_iter().flatten().collect();
                //vec![term::fun(name.clone(), args)]
                unimplemented!()
            }
        }
    }
}

impl AbsInstance {
    pub fn encode_clause(&self, c: super::chc::AbsClause) -> super::chc::AbsClause {
        let mut ctx = EncodeCtx::new(self);
        let (x, y) = ctx.tr_varinfos(&c.vars);
        let lhs_term = ctx.encode(&c.lhs_term);
        for lhs_app in c.lhs_preds.iter() {
            let mut args = Vec::new();
            for arg in lhs_app.args.iter() {
                let temrs = ctx.encode(arg);
            }
        }
    }
}
