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

        // let x_idx = infos.next_index();
        // let info = VarInfo::new("x".to_string(), typ::int(), x_idx);
        // infos.push(info);

        // 0
        Self {
            args: infos,
            terms: vec![term::int_zero()],
        }
    }
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
        format!("{}-{}", ENC_TAG, new_type)
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
    fn get_ith_enc_rdf_name(&self, i: usize) -> String {
        format!("{}-{}", self.generate_fun_name(), i)
    }

    /*
        enc-list-int l = (ite (is-nil l) 0 (ite (is-cons l) (+ 1 (enc-list-int (tail l)))))
        enc-list-int l = (ite (= nil l) 0 (ite (is-cons l) (+ 1 (enc-list-int (tail l)))))
        enc-list-int-0 l = (ite (= (cons x l2) l) (+ 1 (enc-list-int l2)) 0) ←できない？
        (define-fun-rec len_hoice_reserved_fun
      ( (v_0 IList) ) Int
      (ite (not (is-insert v_0)) 0 (+ 1 (len_hoice_reserved_fun (tail v_0))))
    )
         */

    fn gen_rdf_body(
        &self,
        ctx: &EncodeCtx,
        tag: &str,
        cont: Option<Vec<Term>>,
        target_data: Term,
    ) -> Vec<Term> {
        // 1. main part
        let mut args = Vec::new();
        let (ty, prms) = self.typ.dtyp_inspect().unwrap();

        for (sel, ty) in ty.selectors_of(tag).unwrap().iter() {
            let ty = ty.to_type(Some(prms)).unwrap();
            // Example: (head l)
            let term = term::dtyp_slc(ty.clone(), sel, target_data.clone());
            match ctx.encs.get(&ty) {
                Some(enc_for_ty) => {
                    for i in 0..enc_for_ty.n_params {
                        // Example: (enc-list-int-0 (tail l))
                        let f = enc_for_ty.get_ith_enc_rdf_name(i);
                        let arg = term::unsafe_fun(f, vec![term.clone()], typ::int());
                        args.push(arg);
                    }
                }
                None => {
                    // base types
                    args.push(term);
                }
            }
        }
        // apply approx to [(enc-list-int-0 (tail l)); enc-list-int-1 (tail l))];

        let res = self.approxs.get(tag).unwrap().apply(args);
        let cont = match cont {
            Some(cont) => cont,
            None => return res,
        };
        assert_eq!(res.len(), cont.len());

        // 2. ite-part if not last
        // (ite (is-<tag> target_data) res cont)
        let check = term::dtyp_tst(tag, target_data);
        res.into_iter()
            .zip(cont.into_iter())
            .map(|(res, cont)| term::app(Op::Ite, vec![check.clone(), res, cont]))
            .collect()
    }

    /// Define encoding functions in the solver.
    ///
    /// Assumption: Data type `self.typ` has already been defined before.
    pub fn generate_enc_fun(
        &self,
        ctx: &EncodeCtx,
        funs: &mut Vec<(String, Typ, Term)>,
    ) -> Res<()> {
        let mut constructors = self.typ.dtyp_inspect().unwrap().0.news.keys();

        let target_data = term::var(VarIdx::new(0), self.typ.clone());

        let mut terms =
            self.gen_rdf_body(ctx, constructors.next().unwrap(), None, target_data.clone());

        while let Some(constructor) = constructors.next() {
            terms = self.gen_rdf_body(ctx, constructor, Some(terms), target_data.clone())
        }

        assert_eq!(terms.len(), self.n_params);

        for (idx, term) in terms.into_iter().enumerate() {
            let name = self.get_ith_enc_rdf_name(idx);
            funs.push((name, self.typ.clone(), term))
        }

        Ok(())
    }

    pub fn encode_var_with_rdf(&self, varidx: &VarIdx) -> Vec<Term> {
        (0..self.n_params)
            .map(|i| {
                let name = self.get_ith_enc_rdf_name(i);
                term::unsafe_fun(
                    name,
                    vec![term::var(varidx.clone(), self.typ.clone())],
                    typ::int(),
                )
            })
            .collect()
    }
}

pub struct EncodeCtx<'a> {
    encs: &'a BTreeMap<Typ, Enc>,
}

impl<'a> EncodeCtx<'a> {
    /// The first item of the returned tuple is the new vector of variables
    /// The second is the map from the original variable to approximated variables
    pub fn tr_varinfos(&self, varmap: &VarInfos) -> (VarInfos, VarHMap<VarMap<VarInfo>>) {
        let mut new_varmap = VarInfos::new();
        let mut orig2approx_var = VarHMap::new();
        for v in varmap.iter() {
            if let Some(enc) = self.encs.get(&v.typ) {
                let introduced = enc.gen_typ(&mut new_varmap, &v.name);
                orig2approx_var.insert(v.idx, introduced);
            } else {
                // base types (not approximated)
                let mut v = v.clone();
                v.idx = new_varmap.next_index();
                new_varmap.push(v);
            }
        }
        (new_varmap, orig2approx_var)
    }
    pub fn new(encs: &'a BTreeMap<Typ, Enc>) -> Self {
        Self { encs }
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
    fn handle_app<EncodeVar>(
        &self,
        typ: &Typ,
        op: &Op,
        args: impl IntoIterator<Item = &'a Term>,
        encode_var: &EncodeVar,
    ) -> Vec<Term>
    where
        EncodeVar: Fn(&'a Typ, &'a VarIdx) -> Vec<Term>,
    {
        let argss = args
            .into_iter()
            .map(|arg| self.encode(arg, encode_var))
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
    pub fn encode<EncodeVar>(&self, term: &'a Term, encode_var: &EncodeVar) -> Vec<Term>
    where
        EncodeVar: Fn(&'a Typ, &'a VarIdx) -> Vec<Term>,
    {
        match term.get() {
            RTerm::Var(x, y) => {
                encode_var(x, y)

            }
            RTerm::Cst(val) => self.encode_val(val),
            RTerm::App { typ, op, args, .. } => self.handle_app(typ, op, args, encode_var),
            RTerm::DTypNew {
                typ, name, args, ..
            } => {
                let argss = args.iter().map(|arg| self.encode(arg, encode_var)).collect::<Vec<_>>();
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
                let terms = self.encode(t, encode_var);
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
