//! preprocess [Kostyukov+ PLDI21]
//!
//!  - remove all the selectors and testers
//!    - by introducing additional temporary variables
//!  - replace dis-equality on data types with true (temporary solution)
//!     - better solution: introduce a new predicate that expresses the dis-equality on each data type,
//!       which is introduced by Kostyukov et al.
//!
use super::chc::*;
use crate::common::*;
use crate::info::VarInfo;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum Polarity {
    Pos,
    Neg,
}

impl Polarity {
    fn pos() -> Self {
        Polarity::Pos
    }
    fn flip(&self) -> Self {
        match self {
            Polarity::Pos => Polarity::Neg,
            Polarity::Neg => Polarity::Pos,
        }
    }
}

/// Remove dis-equality on data types and replace equality with AdtEql
fn handle_equality(t: &term::Term, pol: Polarity) -> Term {
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => t.clone(),
        RTerm::CArray { typ, term, .. } => {
            let term = handle_equality(term, pol);
            term::cst_array(typ.clone(), term)
        }
        RTerm::App { op, args, .. } => {
            let pol = match op {
                Op::Not => pol.flip(),
                _ => pol,
            };
            let args: Vec<_> = args.iter().map(|t| handle_equality(t, pol)).collect();
            assert!(args.len() > 0);
            let arg = &args[0];
            match op {
                Op::Eql if arg.typ().is_dtyp() => {
                    // replace this to AdtEql if pol = Pos
                    if pol == Polarity::Pos {
                        term::adteq(args[0].clone(), args[1].clone())
                    } else {
                        warn!("Dis-equality on data types is approximated as true");
                        term::bool(false)
                    }
                }
                Op::AdtEql => panic!("AdtEql should not appear in the preprocessed term"),
                _ => term::app(op.clone(), args),
            }
        }
        RTerm::DTypNew {
            typ, name, args, ..
        } => {
            let args = args.iter().map(|t| handle_equality(t, pol)).collect();
            term::dtyp_new(typ.clone(), name, args)
        }
        RTerm::DTypSlc { .. } => todo!(),
        RTerm::DTypTst { .. } => todo!(),
        RTerm::Fun { name, args, .. } => {
            let args = args.iter().map(|t| handle_equality(t, pol)).collect();
            term::fun(name.clone(), args)
        }
    }
}

fn slcs_to_args(
    prms: &dtyp::TPrmMap<Typ>,
    slcs: &[(String, dtyp::PartialTyp)],
    varinfos: &mut VarInfos,
) -> Vec<(VarIdx, Typ)> {
    let mut args = Vec::new();
    // return the index of the selected variable
    for (_, sel_ty) in slcs.iter() {
        let new_var = varinfos.next_index();
        let sel_ty = sel_ty.to_type(Some(prms)).unwrap();
        let new_var_info = VarInfo::new("tmp", sel_ty.clone(), new_var);
        varinfos.push(new_var_info);
        args.push((new_var, sel_ty));
    }
    args
}

fn find_other_selectors<'a>(dty: &'a DTyp, selector: &str) -> Res<(&'a String, &'a dtyp::CArgs)> {
    for (constr_name, slcs) in dty.news.iter() {
        for (sel, _) in slcs.iter() {
            if sel == selector {
                return Ok((constr_name, slcs));
            }
        }
    }
    bail!("Selector {} is not found in the type {}", selector, dty)
}

/// Remove all the selectors and testers
fn remove_slc_tst_inner(
    t: &Term,
    varinfos: &mut VarInfos,
    additional_constrs: &mut Vec<Term>,
) -> Term {
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => t.clone(),
        RTerm::CArray { typ, term, .. } => {
            let term = remove_slc_tst_inner(term, varinfos, additional_constrs);
            term::cst_array(typ.clone(), term)
        }
        RTerm::App { op, args, .. } => {
            let args = args
                .iter()
                .map(|t| remove_slc_tst_inner(t, varinfos, additional_constrs))
                .collect();
            term::app(op.clone(), args)
        }
        RTerm::DTypNew {
            typ, name, args, ..
        } => {
            let args = args
                .iter()
                .map(|t| remove_slc_tst_inner(t, varinfos, additional_constrs))
                .collect();
            term::dtyp_new(typ.clone(), name, args)
        }
        RTerm::DTypSlc { name, term, .. } => {
            let term_typ = term.typ();
            let (dty, prms) = term_typ.dtyp_inspect().unwrap();
            let (constructor_name, slcs) = find_other_selectors(dty, name).unwrap();
            let args = slcs_to_args(prms, slcs, varinfos);

            let idx = slcs
                .iter()
                .enumerate()
                .find_map(|(idx, (sel, _))| if sel == name { Some(idx) } else { None })
                .unwrap();
            let target_arg = args[idx].clone();

            let args = args.into_iter().map(|(v, t)| term::var(v, t)).collect();
            let lhs = term::dtyp_new(term.typ(), constructor_name, args);
            let eq = term::eq(lhs.clone(), term.clone());
            additional_constrs.push(eq);
            term::var(target_arg.0, target_arg.1)
        }
        RTerm::DTypTst { name, term, .. } => {
            let term_typ = term.typ();
            let (ty, prms) = term_typ.dtyp_inspect().unwrap();
            let slcs = ty.selectors_of(name).unwrap();
            let args = slcs_to_args(prms, slcs, varinfos)
                .into_iter()
                .map(|(v, t)| term::var(v, t))
                .collect();
            let lhs = term::dtyp_new(term.typ(), name, args);
            let eq = term::eq(lhs.clone(), term.clone());
            eq
        }
        RTerm::Fun { name, args, .. } => {
            let args = args
                .iter()
                .map(|t| remove_slc_tst_inner(t, varinfos, additional_constrs))
                .collect();
            term::fun(name.clone(), args)
        }
    }
}

fn remove_slc_tst(c: &mut AbsClause) {
    let mut constrs = Vec::new();
    let t = remove_slc_tst_inner(&c.lhs_term, &mut c.vars, &mut constrs);
    for p in c.lhs_preds.iter_mut() {
        let args: Vec<_> = p
            .args
            .iter()
            .map(|t| remove_slc_tst_inner(t, &mut c.vars, &mut constrs))
            .collect();
        let args: VarMap<_> = args.into();
        p.args = args.into();
    }
    constrs.push(t);
    c.lhs_term = term::and(constrs);
}

fn handle_clause(c: &mut AbsClause) {
    remove_slc_tst(c);
    c.lhs_term = handle_equality(&c.lhs_term, Polarity::pos());
}

/*
pub struct AbsClause {
    pub vars: VarInfos,
    pub rhs: Option<(PrdIdx, Vec<VarIdx>)>,
    pub lhs_preds: Vec<PredApp>,
    pub lhs_term: Term,
}
     */
#[test]
fn test_remove_slc_tst() {
    use crate::info::VarInfo;
    let preds = Preds::new();
    let p = preds.next_index();
    let rhs = None;

    // List<T> = nil | insert (head T) (tail List<T>)
    dtyp::create_list_dtyp();

    // ilist
    let ilist = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());

    // P(tail l, head l) /\ is-cons l /\ z = head l => false
    let mut vars = VarInfos::new();
    let l = vars.next_index();
    let li = VarInfo::new("l", ilist.clone(), l);
    vars.push(li);
    let z = vars.next_index();
    let zi = VarInfo::new("z", typ::int(), z);
    vars.push(zi);

    let arg1 = term::dtyp_slc(ilist.clone(), "tail", term::var(l, ilist.clone()));
    let arg2 = term::dtyp_slc(typ::int(), "head", term::var(l, ilist.clone()));
    let args: VarMap<_> = vec![arg1, arg2].into();
    let p = super::chc::PredApp {
        pred: p,
        args: args.into(),
    };

    let term1 = term::dtyp_tst("insert", term::var(l, ilist.clone()));
    let term2 = term::eq(
        term::var(z, typ::int()),
        term::dtyp_slc(typ::int(), "head", term::var(l, ilist.clone())),
    );
    let lhs_term = term::and(vec![term1, term2]);
    let mut c = AbsClause {
        vars,
        rhs,
        lhs_preds: vec![p],
        lhs_term,
    };
    println!("clause: {}", c);
    remove_slc_tst(&mut c);
    println!("transformed: {}", c);

    // check if all the selectors and testers are removed from lhs_term and lhs_preds
    fn check_no_slc_tst(t: &Term) {
        match t.get() {
            RTerm::Var(_, _) | RTerm::Cst(_) => {}
            RTerm::CArray { term, .. } => check_no_slc_tst(term),
            RTerm::App { op, args, .. } => {
                for arg in args.iter() {
                    check_no_slc_tst(arg);
                }
            }
            RTerm::DTypNew { args, .. } => {
                for arg in args.iter() {
                    check_no_slc_tst(arg);
                }
            }
            RTerm::DTypSlc { .. } => panic!("DTypSlc should not appear"),
            RTerm::DTypTst { .. } => panic!("DTypTst should not appear"),
            RTerm::Fun { args, .. } => {
                for arg in args.iter() {
                    check_no_slc_tst(arg);
                }
            }
        }
    }
    for p in c.lhs_preds.iter() {
        for arg in p.args.iter() {
            check_no_slc_tst(arg);
        }
    }
    check_no_slc_tst(&c.lhs_term);
}

pub fn work<'a>(instance: &mut AbsInstance<'a>) {
    for c in instance.clauses.iter_mut() {
        handle_clause(c);
    }
}
