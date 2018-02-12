//! Term creation functions.

use hashconsing::{ HashConsign, HConser } ;

use common::* ;
use term::{ RTerm, Term, Op } ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RTerm> > ;

lazy_static! {
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
}

lazy_static! {
  /// Cache for terms' variables.
  static ref var_cache: RwLock< HConMap<Term, VarSet> > = RwLock::new(
    HConMap::with_capacity( conf.instance.term_capa )
  ) ;
}


/// Scans a term to extract the variables that appear in it.
fn scan_vars(t: & Term) -> VarSet {
  let mut to_do = vec![ t ] ;
  let mut set = VarSet::with_capacity(11) ;
  while let Some(term) = to_do.pop() {
    match ** term {
      RTerm::Var(i) => {
        let _ = set.insert(i) ; ()
      },
      RTerm::Int(_) => (),
      RTerm::Real(_) => (),
      RTerm::Bool(_) => (),
      RTerm::App{ ref args, .. } => for arg in args {
        to_do.push(arg)
      },
    }
  }
  set.shrink_to_fit() ;
  set
}

/// Variables appearing in a term (cached).
#[inline]
pub fn vars(t: & Term) -> VarSet {
  if let Some(vars) = var_cache.read().expect(
    "variable cache is corrupted..."
  ).get(t) {
    return vars.clone()
  }
  var_cache.write().expect(
    "variable cache is corrupted..."
  ).entry( t.clone() ).or_insert_with(
    || scan_vars(t)
  ).clone()
}

/// Map over the variables appearing in a term (cached).
#[inline]
pub fn map_vars<F>(t: & Term, mut f: F)
where F: FnMut(VarIdx) {
  if let Some(vars) = var_cache.read().expect(
    "variable cache is corrupted..."
  ).get(t) {
    for var in vars {
      f(* var)
    }
    return ()
  }

  let vars = scan_vars(t) ;
  for var in & vars {
    f(* var)
  }
  var_cache.write().expect(
    "variable cache is corrupted..."
  ).entry( t.clone() ).or_insert_with(
    || vars
  ) ;
  ()
}

/// Creates a term.
#[inline(always)]
pub fn term(t: RTerm) -> Term {
  factory.mk(t)
}

/// Creates a variable.
#[inline(always)]
pub fn var<V: Into<VarIdx>>(v: V) -> Term {
  factory.mk( RTerm::Var(v.into()) )
}

/// Creates an integer constant.
#[inline(always)]
pub fn int<I: Into<Int>>(i: I) -> Term {
  factory.mk(
    RTerm::Int( i.into() )
  )
}
/// Creates a real constant.
#[inline(always)]
pub fn real<R: Into<Rat>>(r: R) -> Term {
  let r = r.into() ;
  let r = if r.numer().is_negative() == r.denom().is_negative() {
    r
  } else {
    - r.abs()
  } ;
  factory.mk( RTerm::Real(r) )
}
/// Creates the constant `0`.
#[inline(always)]
pub fn zero() -> Term {
  int( Int::zero() )
}
/// Creates the constant `1`.
#[inline(always)]
pub fn one() -> Term {
  int( Int::one() )
}

/// Creates a boolean.
#[inline(always)]
pub fn bool(b: bool) -> Term {
  factory.mk( RTerm::Bool(b) )
}
/// Creates the constant `true`.
#[inline(always)]
pub fn tru() -> Term {
  bool(true)
}
/// Creates the constant `false`.
#[inline(always)]
pub fn fls() -> Term {
  bool(false)
}

/// If-then-else.
#[inline(always)]
pub fn ite(c: Term, t: Term, e: Term) -> Term {
  app(Op::Ite, vec![c, t, e])
}

/// Implication.
#[inline(always)]
pub fn implies(lhs: Term, rhs: Term) -> Term {
  app(Op::Impl, vec![lhs, rhs])
}

/// Negates a term.
#[inline(always)]
pub fn not(term: Term) -> Term {
  app(Op::Not, vec![term])
}
/// Disjunction.
#[inline(always)]
pub fn or(terms: Vec<Term>) -> Term {
  app(Op::Or, terms)
}
/// Conjunction.
#[inline(always)]
pub fn and(terms: Vec<Term>) -> Term {
  app(Op::And, terms)
}

/// Creates an operator application.
///
/// Runs [`normalize`](fn.normalize.html) and returns its result.
#[inline(always)]
pub fn app(op: Op, args: Vec<Term>) -> Term {
  normalize(op, args)
}

/// Creates a less than or equal to.
#[inline(always)]
pub fn le(lhs: Term, rhs: Term) -> Term {
  app(Op::Le, vec![lhs, rhs])
}
/// Creates a less than.
#[inline(always)]
pub fn lt(lhs: Term, rhs: Term) -> Term {
  app(Op::Lt, vec![lhs, rhs])
}
/// Creates a greater than.
#[inline(always)]
pub fn gt(lhs: Term, rhs: Term) -> Term {
  app(Op::Gt, vec![lhs, rhs])
}
/// Creates a greater than or equal to.
#[inline(always)]
pub fn ge(lhs: Term, rhs: Term) -> Term {
  app(Op::Ge, vec![lhs, rhs])
}

/// Creates an equality.
#[inline(always)]
pub fn eq(lhs: Term, rhs: Term) -> Term {
  app(Op::Eql, vec![lhs, rhs])
}

/// Creates a sum.
#[inline(always)]
pub fn add(kids: Vec<Term>) -> Term {
  app(Op::Add, kids)
}
/// Creates a subtraction.
#[inline(always)]
pub fn sub(kids: Vec<Term>) -> Term {
  app(Op::Sub, kids)
}
/// Creates a unary minus.
#[inline(always)]
pub fn u_minus(kid: Term) -> Term {
  app(Op::Sub, vec![kid])
}
/// Creates a multiplication.
#[inline(always)]
pub fn mul(kids: Vec<Term>) -> Term {
  app(Op::Mul, kids)
}
/// Creates an integer division.
#[inline(always)]
pub fn idiv(kids: Vec<Term>) -> Term {
  app(Op::IDiv, kids)
}
/// Creates a division.
#[inline(always)]
pub fn div(kids: Vec<Term>) -> Term {
  app(Op::Div, kids)
}
/// Creates a modulo application.
#[inline(always)]
pub fn modulo(a: Term, b: Term) -> Term {
  app(Op::Mod, vec![a, b])
}

/// Creates a conversion from `Int` to `Real`.
#[inline(always)]
pub fn to_real(int: Term) -> Term {
  app(Op::ToReal, vec![int])
}
/// Creates a conversion from `Real` to `Int`.
#[inline(always)]
pub fn to_int(real: Term) -> Term {
  app(Op::ToInt, vec![real])
}







/// Simplifies operator applications.
///
/// This function is currently not strongly-normalizing.
///
/// # Examples
///
/// ```rust
/// use hoice::term ;
///
/// let tru = term::tru() ;
/// let fls = term::fls() ;
/// 
/// let var_1 = term::var(7) ;
/// let n_var_1 = term::not( var_1.clone() ) ;
/// let var_2 = term::var(2) ;
/// let n_var_2 = term::not( var_2.clone() ) ;
///
/// let int_1 = term::int(3) ;
/// let int_2 = term::int(42) ;
///
///
/// // |===| `And` and `Or`.
///
/// // Nullary.
/// assert_eq!( tru, term::and( vec![] ) ) ;
/// assert_eq!( fls, term::or( vec![] ) ) ;
///
/// // Unary.
/// assert_eq!( var_2, term::and( vec![ var_2.clone() ] ) ) ;
/// assert_eq!( var_1, term::or( vec![ var_1.clone() ] ) ) ;
///
/// // Trivial.
/// assert_eq!(
///   fls, term::and( vec![ var_1.clone(), fls.clone(), var_2.clone() ] )
/// ) ;
/// assert_eq!(
///   tru, term::or( vec![ var_1.clone(), tru.clone(), var_2.clone() ] )
/// ) ;
///
///
/// // |===| `Ite`.
///
/// // Trivial.
/// assert_eq!(
///   var_1, term::ite( tru.clone(), var_1.clone(), var_2.clone() )
/// ) ;
/// assert_eq!(
///   var_2, term::ite( fls.clone(), var_1.clone(), var_2.clone() )
/// ) ;
/// assert_eq!( // Same `then` and `else`.
///   var_1, term::ite( var_2.clone(), var_1.clone(), var_1.clone() )
/// ) ;
///
///
/// // |===| `Not`.
///
/// // Double negation.
/// assert_eq!( var_1, term::not( n_var_1.clone() ) ) ;
/// assert_eq!( n_var_1, term::not( var_1.clone() ) ) ;
///
/// // `And` and `Or` propagation.
/// let and = term::and( vec![ var_1.clone(), var_2.clone() ] ) ;
/// let or = term::or( vec![ var_1.clone(), var_2.clone() ] ) ;
/// let n_and = term::not( and.clone() ) ;
/// let n_or = term::not( or.clone() ) ;
/// let and_n = term::and( vec![ n_var_1.clone(), n_var_2.clone() ] ) ;
/// let or_n = term::or( vec![ n_var_1.clone(), n_var_2.clone() ] ) ;
/// assert_eq!( n_and, or_n ) ;
/// assert_eq!( n_or, and_n ) ;
/// assert_eq!( and, term::not( or_n ) ) ;
/// assert_eq!( and, term::not( n_and ) ) ;
/// assert_eq!( or, term::not( and_n ) ) ;
/// assert_eq!( or, term::not( n_or ) ) ;
///
///
/// // |===| `Eql`.
///
/// // `t_1 = t_1`.
/// assert_eq!( tru, term::eq(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( tru, term::eq(int_1.clone(), int_1.clone()) ) ;
/// // `n != m` with `n` and `m` integers.
/// assert_eq!( fls, term::eq(int_1.clone(), int_2.clone()) ) ;
/// // `true = t`.
/// assert_eq!( var_1, term::eq(tru.clone(), var_1.clone()) ) ;
/// // `false = t`.
/// assert_eq!( n_var_1, term::eq(fls.clone(), var_1.clone()) ) ;
///
///
/// // |===| `Ge`, `Le`, `Lt` and `Gt`.
///
/// assert_eq!( tru, term::ge(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( tru, term::le(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( fls, term::gt(var_1.clone(), var_1.clone()) ) ;
/// assert_eq!( fls, term::lt(var_1.clone(), var_1.clone()) ) ;
///
/// assert_eq!( fls, term::ge(int_1.clone(), int_2.clone()) ) ;
/// assert_eq!( tru, term::le(int_1.clone(), int_2.clone()) ) ;
/// assert_eq!( fls, term::gt(int_1.clone(), int_2.clone()) ) ;
/// assert_eq!( tru, term::lt(int_1.clone(), int_2.clone()) ) ;
/// ```
pub fn normalize(
  op: Op, args: Vec<Term>
) -> Term {

  // Contains stack frames composed of
  //
  // - the operator `op` to apply,
  // - a vector of operators to apply to some arguments before applying `op`
  // - the arguments to apply `op`, basically storing the results of the
  //   applications from the second element
  //
  // It is important that the second, `to_do`, element of the frames is in
  // **reverse order**. This is because its elements will be `pop`ped and
  // `push`ed on the third element.
  let mut stack = vec![ (op, vec![], args) ] ;

  'go_down: while let Some((op, mut to_do, mut args)) = stack.pop() {

    'do_stuff: loop {

      match to_do.pop() {
        Some( NormRes::Term(term) ) => {
          args.push(term) ;
          continue 'do_stuff
        },

        Some( NormRes::App(nu_op, nu_to_do) ) => {
          stack.push( (op, to_do, args) ) ;
          let nu_args = Vec::with_capacity( nu_to_do.len() ) ;
          stack.push( (nu_op, nu_to_do, nu_args) ) ;
          continue 'go_down
        },

        None => match normalize_app(op, args) {
          // Going down...
          NormRes::App(op, mut to_do) => {
            let args = Vec::with_capacity( to_do.len() ) ;
            to_do.reverse() ;
            stack.push( (op, to_do, args) ) ;
            continue 'go_down
          },
          // Going up...
          NormRes::Term(term) => if let Some(
            & mut ( _, _, ref mut args )
          ) = stack.last_mut() {
            args.push( term ) ;
            continue 'go_down
          } else {
            return term
          },
        },
      }

    }

  }

  unreachable!()
}



/// Normalization result.
enum NormRes {
  /// Just a term.
  Term(Term),
  /// More stuff to do.
  App(Op, Vec<NormRes>),
}



/// Normalizes an operation application.
fn normalize_app(op: Op, mut args: Vec<Term>) -> NormRes {
  use num::Zero ;

  let (op, args) = match op {

    Op::Ite => if args.len() == 3 {
      if let Some(b) = args[0].bool() {
        return NormRes::Term(
          if b { args[1].clone() } else { args[2].clone() }
        )
      }
      if args[1] == args[2] {
        return NormRes::Term( args[1].clone() )
      }
      (op, args)
    } else {
      panic!(
        "trying to apply `Ite` operator to {} (!= 3) arguments", args.len()
      )
    },

    Op::Impl => match (args.pop(), args.pop()) {
      (Some(rgt), Some(lft)) => {
        debug_assert! { args.pop().is_none() }
        return NormRes::App(
          Op::Or, vec![
            NormRes::App(Op::Not, vec![ NormRes::Term(lft) ]),
            NormRes::Term(rgt)
          ]
        )
      },
      _ => panic!("illegal application of `Impl` to less than 2 arguments")
    },

    Op::And => {
      let mut set = HConSet::<Term>::new() ;
      let mut cnt = 0 ;
      
      while cnt < args.len() {
        let is_new = set.insert( args[cnt].clone() ) ;

        if ! is_new {
          args.swap_remove(cnt) ;
          ()
        } else if let Some(b) = args[cnt].bool() {
          if b {
            args.swap_remove(cnt) ;
            ()
          } else {
            return NormRes::Term( fls() )
          }
        } else {
          cnt += 1
        }
      }

      if args.is_empty() {
        return NormRes::Term( term::tru() )
      } else if args.len() == 1 {
        return NormRes::Term( args.pop().unwrap() )
      } else {
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Or => {
      let mut set = HConSet::<Term>::new() ;
      let mut cnt = 0 ;
      
      while cnt < args.len() {
        let is_new = set.insert( args[cnt].clone() ) ;

        if ! is_new {
          args.swap_remove(cnt) ;
          ()
        } else if let Some(b) = args[cnt].bool() {
          if ! b {
            args.swap_remove(cnt) ;
            ()
          } else {
            return NormRes::Term( tru() )
          }
        } else {
          cnt += 1
        }
      }

      if args.is_empty() {
        return NormRes::Term( term::fls() )
      } else if args.len() == 1 {
        return NormRes::Term( args.pop().unwrap() )
      } else {
        args.sort_unstable() ;
        (op, args)
      }
    },

    Op::Not => {
      assert!( args.len() == 1 ) ;
      if let Some(b) = args[0].bool() {
        return NormRes::Term( bool(! b) )
      }

      match * args[0] {
        RTerm::App { op: Op::Not, ref args } => {
          return NormRes::Term( args[0].clone() )
        },

        RTerm::App { op: Op::And, ref args } => {
          return NormRes::App(
            Op::Or, args.iter().map(
              |arg| NormRes::App(
                Op::Not, vec![ NormRes::Term( arg.clone() ) ]
              )
            ).collect()
          )
        },
        RTerm::App { op: Op::Or, ref args } => {
          return NormRes::App(
            Op::And, args.iter().map(
              |arg| NormRes::App(
                Op::Not, vec![ NormRes::Term( arg.clone() ) ]
              )
            ).collect()
          )
        },

        RTerm::App { op: Op::Gt, ref args } => {
          let mut args = args.clone() ;
          args.reverse() ;
          return NormRes::Term((
            factory.mk(
              RTerm::App { op: Op::Ge, args }
            )
          ))
        },
        RTerm::App { op: Op::Ge, ref args } => {
          let mut args = args.clone() ;
          args.reverse() ;
          return NormRes::Term((
            factory.mk(
              RTerm::App { op: Op::Gt, args }
            )
          ))
        },
        _ => (),
      }

      (op, args)
    },

    Op::Eql => {
      if args.len() == 2 {
        if args[0] == args[1] {
          return NormRes::Term( tru() )
        } else

        if let Some(b) = args[0].bool() {
          return NormRes::Term(
            if b {
              args[1].clone()
            } else {
              not( args[1].clone() )
            }
          )
        } else

        if let Some(b) = args[1].bool() {
          return NormRes::Term(
            if b {
              args[0].clone()
            } else {
              not( args[0].clone() )
            }
          )
        } else

        if let (Some(i_1), Some(i_2)) = (
          args[0].int(), args[1].int()
        ) {
          return NormRes::Term( term::bool( i_1 == i_2 ) )
        } else

        if let (Some(r_1), Some(r_2)) = (
          args[0].real(), args[1].real()
        ) {
          return NormRes::Term( term::bool( r_1 == r_2 ) )
        } else

        if let Some((var, term)) = args[0].invert( args[1].clone() ) {
          args = vec![ term::var(var), term ]
        } else

        if let Some((var, term)) = args[1].invert( args[0].clone() ) {
          args = vec![ term::var(var), term ]
        }
      }
      args.sort_unstable() ;
      (op, args)
    },

    Op::Sub => {
      let mut args = args.into_iter() ;
      if let Some(first) = args.next() {

        if args.len() == 0 {
          if let Some(i) = first.int_val() {
            return NormRes::Term( int(- i) )
          } else if let Some(r) = first.real_val() {
            return NormRes::Term( real( -r ) )
          }

          return NormRes::App(
            Op::Mul, vec![
              NormRes::Term( term::int(- 1) ),
              NormRes::Term(first),
            ]
          )
        } else {
          let mut to_do = Vec::with_capacity( args.len() + 1 ) ;
          to_do.push( NormRes::Term(first) ) ;
          for arg in args {
            to_do.push(
              NormRes::App(
                Op::Mul, vec![
                  NormRes::Term( term::int(- 1) ),
                  NormRes::Term(arg),
                ]
              )
            )
          }

          return NormRes::App(Op::Add, to_do)
        }

      } else {
        panic!("illegal nullary application of `Sub`")
      }
    },

    Op::Add => if args.is_empty() {
      panic!("trying to construct an empty sum")
    } else {

      let mut cnt = 0 ;
      let (mut int_sum, mut rat_sum): (Option<Int>, Option<Rat>) = (
        None, None
      ) ;

      macro_rules! sum {
        (add int $e:expr) => (
          int_sum = Some(
            int_sum.unwrap_or( Int::zero() ) + $e
          )
        ) ;
        (add real $e:expr) => (
          rat_sum = Some(
            rat_sum.unwrap_or( Rat::zero() ) + $e
          )
        ) ;
        (get) => (
          match (int_sum, rat_sum) {
            ( Some(i), None ) => if i.is_zero() {
              None
            } else {
              Some( term::int(i) )
            },
            ( None, Some(r) ) => if r.is_zero() {
              None
            } else {
              Some( term::real(r) )
            },
            ( Some(i), Some(r) ) => {
              let r = r + Rat::new(i, 1.into()) ;
              if r.is_zero() {
                None
              } else {
                Some( term::real(r) )
              }
            },
            (None, None) => None,
          }
        ) ;
      }

      while cnt < args.len() {
        if let Some(kids) = args[cnt].add_inspect().map(|kids| kids.clone()) {
          args.swap_remove(cnt) ;
          args.extend(kids)
        } else if let Some(i) = args[cnt].int_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          sum! { add int i }
        } else if let Some(r) = args[cnt].real_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          sum! { add real r }
        } else {
          cnt += 1
        }
      }

      if args.len() == 0 {
        if let Some(sum) = sum!(get) {
          return NormRes::Term(sum)
        } else {
          return NormRes::Term( int(0) )
        }
      } else if args.len() == 1 {
        if let Some(sum) = sum!(get) {
          args.push(sum) ;
          args.sort_unstable() ;
          (op, args)
        } else {
          return NormRes::Term( args.pop().unwrap() )
        }
      } else {
        if let Some(sum) = sum!(get) {
          args.push(sum)
        }
        args.sort_unstable() ;
        (op, args)
      }

    },

    Op::Mul => if args.is_empty() {
      panic!("trying to construct an empty multiplication")
    } else {

      let mut cnt = 0 ;
      let (mut int_coef, mut rat_coef): (Option<Int>, Option<Rat>) = (
        None, None
      ) ;

      macro_rules! coef {
        (mul int $e:expr) => (
          int_coef = Some(
            int_coef.unwrap_or( Int::one() ) * $e
          )
        ) ;
        (mul real $e:expr) => (
          rat_coef = Some(
            rat_coef.unwrap_or( Rat::one() ) * $e
          )
        ) ;
        (get) => (
          match (int_coef, rat_coef) {
            ( Some(i), None ) => if i == Int::one() {
              None
            } else if i.is_zero() {
              return NormRes::Term( int(0) )
            } else {
              Some( term::int(i) )
            },
            ( None, Some(r) ) => if r == Rat::one() {
              None
            } else if r.is_zero() {
              return NormRes::Term(
                real( Rat::new(0.into(), 1.into() ) )
              )
            } else {
              Some( term::real(r) )
            },
            ( Some(i), Some(r) ) => {
              let r = r * Rat::new(i, 1.into()) ;
              if r == Rat::one() {
                None
              } else if r.is_zero() {
                return NormRes::Term( int(0) )
              } else {
                Some( term::real(r) )
              }
            },
            (None, None) => None,
          }
        ) ;
      }

      while cnt < args.len() {
        if let Some(kids) = args[cnt].mul_inspect().map(|kids| kids.clone()) {
          args.swap_remove(cnt) ;
          args.extend(kids)
        } else if let Some(i) = args[cnt].int_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          coef! { mul int i }
        } else if let Some(r) = args[cnt].real_val().map( |v| v.clone() ) {
          args.swap_remove(cnt) ;
          coef! { mul real r }
        } else {
          cnt += 1
        }
      }

      if args.len() == 0 {
        if let Some(coef) = coef!(get) {
          return NormRes::Term(coef)
        } else {
          return NormRes::Term( int(1) )
        }
      } else if args.len() == 1 {
        if let Some(coef) = coef!(get) {
          if let Some(args) = args[0].add_inspect() {
            return NormRes::App(
              Op::Add, args.iter().map(
                |arg| NormRes::App(
                  Op::Mul, vec![
                    NormRes::Term(coef.clone()),
                    NormRes::Term(arg.clone()),
                  ]
                )
              ).collect()
            )
          }
          args.push(coef) ;
          args.sort_unstable() ;
          (op, args)
        } else {
          return NormRes::Term( args.pop().unwrap() )
        }
      } else {
        if let Some(coef) = coef!(get) {
          args.push(coef)
        }
        args.sort_unstable() ;
        (op, args)
      }

    },

    Op::IDiv => if args.len() == 2 {
      macro_rules! num_den {
        () => (
          if let ( Some(den), Some(num) ) = (
            args.pop(), args.pop()
          ) {
            (num, den)
          } else {
            panic!("logic error, pop failed after length check")
          }
        )
      }

      match ( args[0].int(), args[1].int() ) {
        ( Some(num), Some(den) ) => match Op::IDiv.eval(
          vec![ Val::I( num.clone() ), Val::I( den.clone() ) ]
        ) {
          Ok( Val::I(i) ) => return NormRes::Term( int(i) ),
          Ok(_) => panic!(
            "unexpected result while evaluating `({} {} {})`", op, num, den
          ),
          Err(e) => panic!(
            "error while evaluating `({} {} {})`: {}",
            op, num, den, e.description()
          ),
        },

        ( Some(num), _ ) => if num.is_zero() {
          return NormRes::Term( int(0) )
        },

        ( _, Some(den) ) => if den.abs() == Int::one() {
          let (num, _) = num_den!() ;
          if den.is_negative() {
            return NormRes::App( Op::Sub, vec![ NormRes::Term(num) ] )
          } else {
            return NormRes::Term(num)
          }
        },

        ( None, None ) => (),
      }

      (op, args)
    } else {
      panic!(
        "illegal application of `{}` to {} (!= 2) arguments", op, args.len()
      )
    },

    Op::Div => if args.len() != 2 {
      panic!(
        "illegal application of `{}` to {} (!= 2) arguments",
        op, args.len()
      )
    } else if let Some(den) = args[1].int() {
      if den.is_zero() {
        panic!("illegal division by zero")
      }

      let one = Int::one() ;

      if & den == & one {
        if let ( _, Some(num) ) = ( args.pop(), args.pop() ) {
          debug_assert! { args.pop().is_none() }
          return NormRes::Term(num)
        } else {
          panic!("logic error, pop failed after length check")
        }
      }

      if den == - & one {
        if let ( _, Some(num) ) = ( args.pop(), args.pop() ) {
          debug_assert! { args.pop().is_none() }
          return NormRes::App(
            Op::Mul, vec![
              NormRes::Term( term::int(-1) ),
              NormRes::Term(num),
            ]
          )
        } else {
          panic!("logic error, pop failed after length check")
        }
      }

      if let (
        Some(num), Some(den)
      ) = (args[0].int(), args[1].int()) {
        if den.is_zero() {
          panic!("illegal division by zero")
        }

        if ( & num % & den ).is_zero() {
          return NormRes::Term(
            term::int( num / den )
          )
        }
      }

      (op, args)
    } else {
      (op, args)
    },

    Op::Ge => if args.len() == 2 {
      if args[0] == args[1] {
        return NormRes::Term( tru() )
      } else if let (Some(lhs), Some(rhs)) = (
        args[0].int(), args[1].int()
      ) {
        return NormRes::Term( bool(lhs >= rhs) )
      } else if let (Some(lhs), Some(rhs)) = (
        args[0].real(), args[1].real()
      ) {
        return NormRes::Term( bool(lhs >= rhs) )
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::Gt => if args.len() == 2 {
      if args[0] == args[1] {
        return NormRes::Term( fls() )
      } else if let (Some(lhs), Some(rhs)) = (
        args[0].int(), args[1].int()
      ) {
        return NormRes::Term( bool(lhs > rhs) )
      } else if let (Some(lhs), Some(rhs)) = (
        args[0].real(), args[1].real()
      ) {
        return NormRes::Term( bool(lhs > rhs) )
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::Le => {
      if args.len() == 2 {
        if args[0] == args[1] {
          return NormRes::Term( tru() )
        } else if let (Some(lhs), Some(rhs)) = (
          args[0].int(), args[1].int()
        ) {
          return NormRes::Term( bool(lhs <= rhs) )
        } else if let (Some(lhs), Some(rhs)) = (
          args[0].real(), args[1].real()
        ) {
          return NormRes::Term( bool(lhs <= rhs) )
        }
      }
      args.reverse() ;
      (Op::Ge, args)
    },

    Op::Lt => {
      if args.len() == 2 {
        if args[0] == args[1] {
          return NormRes::Term( fls() )
        } else if let (Some(lhs), Some(rhs)) = (
          args[0].int(), args[1].int()
        ) {
          return NormRes::Term( bool(lhs < rhs) )
        } else if let (Some(lhs), Some(rhs)) = (
          args[0].real(), args[1].real()
        ) {
          return NormRes::Term( bool(lhs < rhs) )
        }
      }
      args.reverse() ;
      (Op::Gt, args)
    },

    Op::Mod => if args.len() == 2 {
      if let Some(i) = args[1].int() {
        if i == 1.into() {
          return NormRes::Term( term::int(0) )
        } else {
          (op, args)
        }
      } else {
        (op, args)
      }
    } else {
      (op, args)
    },

    Op::ToInt => {
      if args.len() == 1 {
        if let Some(r) = args[0].real() {
          let mut i = r.to_integer() ;
          if i.is_negative() {
            i = - i
          }
          return NormRes::Term( term::int(i) )
        }
      }
      (op, args)
    },
    Op::ToReal => {
      if args.len() == 1 {
        if let Some(i) = args[0].int() {
          return NormRes::Term(
            term::real( Rat::new(i, 1.into()) )
          )
        }
      }
      (op, args)
    },

    Op::Rem => (op, args),

  } ;

  NormRes::Term( factory.mk( RTerm::App { op, args } ) )
}
