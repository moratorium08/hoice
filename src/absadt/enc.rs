use crate::common::{smt::FullParser as Parser, *};

use crate::common::*;
use crate::info::{Pred, VarInfo};

use super::chc::AbsInstance;

const ENC_TAG: &str = "enc!";

#[derive(Debug, Clone)]
pub struct Approx {
    /// Definition of the arguments
    pub args: VarInfos,
    /// n terms for approximation
    pub terms: Vec<Term>,
}

impl fmt::Display for Approx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "λ")?;
        for arg in self.args.iter() {
            write!(f, "{}: {}, ", arg.name, arg.typ)?;
        }
        write!(f, ". (")?;
        for term in self.terms.iter() {
            write!(f, "{}, ", term)?;
        }
        write!(f, ")")
    }
}

impl Approx {
    pub fn new(args: VarInfos, terms: Vec<Term>) -> Self {
        Self { args, terms }
    }
    /// Length for cons (of type Int List).
    ///
    /// Used for tests
    pub fn len_cons() -> Self {
        let mut infos = VarInfos::new();

        let l_idx = infos.next_index();
        let info = VarInfo::new("l".to_string(), typ::int(), l_idx);
        infos.push(info);

        let x_idx = infos.next_index();
        let info = VarInfo::new("x".to_string(), typ::int(), x_idx);
        infos.push(info);

        // l + 1
        let l = term::var(l_idx, typ::int());
        let one = term::cst(val::int(1));
        let l_plus_one = term::app(Op::Add, vec![l, one]);
        println!("len_cons: {}", l_plus_one);
        Self {
            args: infos,
            terms: vec![l_plus_one],
        }
    }
    /// Length for nil (of type Int List).
    ///
    /// Used for tests.
    pub fn len_nil() -> Self {
        let mut infos = VarInfos::new();

        let x_idx = infos.next_index();
        let info = VarInfo::new("x".to_string(), typ::int(), x_idx);
        infos.push(info);

        println!("len_nil: {}", term::int_zero());
        // 0
        Self {
            args: infos,
            terms: vec![term::int_zero()],
        }
    }
    pub fn apply(&self, arg_terms: Vec<Term>) -> Vec<Term> {
        println!("apply");
        for arg in arg_terms.iter() {
            println!("{}", arg);
        }
        let mut res = Vec::with_capacity(self.terms.len());
        for term in self.terms.iter() {
            println!("try subst: {}", term);
            let subst_map: VarHMap<_> = self
                .args
                .iter()
                .map(|x| x.idx)
                .zip(arg_terms.iter().cloned())
                .collect();
            res.push(term.subst_total(&subst_map).unwrap().0);
        }
        println!("res");
        for t in res.iter() {
            println!("{}", t);
        }
        res
    }
}

/// Enc is an encoding of ADT terms to integer expressions.
///
/// Assumption: typ is a monomorphic type.
#[derive(Debug, Clone)]
pub struct Enc {
    /// Number of parameters for approximation
    pub typ: Typ,
    pub n_params: usize,
    pub approxs: BTreeMap<String, Approx>,
}

impl Enc {
    fn generate_fun_name(&self) -> String {
        let s = self.typ.to_string();
        let mut new_type = String::with_capacity(s.capacity());
        for c in s.chars() {
            if c.is_alphanumeric() {
                new_type.push(c);
            }
        }
        new_type
    }
    pub fn push_approx_typs(&self, varmap: &mut VarMap<Typ>) {
        for _ in 0..self.n_params {
            varmap.push(typ::int());
        }
    }
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

    pub fn len_ilist(ilist_typ: Typ) -> Self {
        let mut approxs = BTreeMap::new();
        approxs.insert("cons".to_string(), Approx::len_cons());
        approxs.insert("nil".to_string(), Approx::len_nil());
        Self {
            typ: ilist_typ,
            n_params: 1,
            approxs,
        }
    }
    /*
        (define-fun-rec
       fac ((x Int)) Int
       (
        ite (<= x 1)
            1
            (* x (fac (- x 1)))
       )
    )

    (assert (= (fac 4) 24))

    (check-sat)

         */
    pub fn write<W>(&self, w: &mut W) -> Res<()>
    where
        W: std::io::Write,
    {
        writeln!(w, "; Enc for {}", self.typ)?;
        for i in 0..self.n_params {
            writeln!(w, "(define-fun-rec")?;
            writeln!(w, "{}-{}-{}", ENC_TAG, self.generate_fun_name(), i)?;
            writeln!(w, "((x {}))", self.typ)?;
            writeln!(w, "\n) Int")?;

            println!("current datatype: {}", self.typ);
            for (tag, approx) in self.approxs.iter() {
                println!("(ite (is-{} x) )", tag);
            }
        }

        Ok(())
    }
    /// Assumption: Data types used in cex are already defined.
    pub fn define_enc_fun(&self, solver: &mut Solver<Parser>) -> Res<()> {
        let mut funs = Vec::with_capacity(self.n_params);
        let base_fun_name = self.generate_fun_name();
        let typ = self.typ.to_string();
        for i in 0..self.n_params {
            let name = format!("{}-{}-{}", ENC_TAG, base_fun_name, i);
            let args = vec![("x", &typ)];
            let ret = "Int";
            // todo
            let body = "1";
            funs.push((name, args, ret, body));
        }
        solver.define_funs_rec(funs)?;

        Ok(())
    }
}

pub struct EncodeCtx<'a> {
    encs: &'a BTreeMap<Typ, Enc>,
    pub introduced: VarHMap<VarMap<VarInfo>>,
}

impl<'a> EncodeCtx<'a> {
    pub fn tr_varinfos(&mut self, varmap: &VarInfos) -> VarInfos {
        let mut new_varmap = VarInfos::new();
        let mut orig2approx_var = VarHMap::new();
        for v in varmap.iter() {
            if let Some(enc) = self.encs.get(&v.typ) {
                let introduced = enc.gen_typ(&mut new_varmap, &v.name);
                orig2approx_var.insert(v.idx, introduced);
            } else {
                // base types (not approximated)
                new_varmap.push(v.clone());
            }
        }
        self.introduced = orig2approx_var;
        new_varmap
    }
    pub fn new(encs: &'a BTreeMap<Typ, Enc>) -> Self {
        Self {
            encs,
            introduced: VarHMap::new(),
        }
    }
    fn encode_val(&self, val: &Val) -> Vec<Term> {
        match val.get() {
            val::RVal::N(_) => todo!(),
            val::RVal::B(_) | val::RVal::I(_) | val::RVal::R(_) | val::RVal::Array { .. } => {
                vec![term::cst(val.clone())]
            }
            val::RVal::DTypNew { typ, name, args } => match self.encs.get(typ) {
                Some(enc) => {
                    let approx = enc.approxs.get(name).unwrap();
                    let mut new_args = Vec::new();
                    for arg in args.iter() {
                        for encoded in self.encode_val(arg) {
                            new_args.push(encoded);
                        }
                    }
                    approx.apply(new_args)
                }
                None => unimplemented!("no encoding for {}", name),
            },
        }
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
        let enc = if let Some(enc) = self.encs.get(typ) {
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
