use super::chc::*;
use crate::common::*;

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

fn handle_term(t: &term::Term, pol: Polarity) -> Term {
    match t.get() {
        RTerm::Var(_, _) | RTerm::Cst(_) => t.clone(),
        RTerm::CArray { typ, term, .. } => {
            let term = handle_term(term, pol);
            term::cst_array(typ.clone(), term)
        }
        RTerm::App { op, args, .. } => {
            let pol = match op {
                Op::Not => pol.flip(),
                _ => pol,
            };
            let args: Vec<_> = args.iter().map(|t| handle_term(t, pol)).collect();
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
            let args = args.iter().map(|t| handle_term(t, pol)).collect();
            term::dtyp_new(typ.clone(), name, args)
        }
        RTerm::DTypSlc { .. } => todo!(),
        RTerm::DTypTst { .. } => todo!(),
        RTerm::Fun { name, args, .. } => {
            let args = args.iter().map(|t| handle_term(t, pol)).collect();
            term::fun(name.clone(), args)
        }
    }
}

fn handle_clause(c: &mut AbsClause) {
    c.lhs_term = handle_term(&c.lhs_term, Polarity::pos());
}

pub fn work<'a>(instance: &mut AbsInstance<'a>) {
    for c in instance.clauses.iter_mut() {
        handle_clause(c);
    }
}
