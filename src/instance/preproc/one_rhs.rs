//! One rhs module.


use common::* ;
use instance::{
  instance::PreInstance, preproc::{
    RedStrat, utils::ExtractRes
  },
} ;






/// Works on predicates that appear in only one rhs.
///
/// # Examples
///
/// | Clause                             | `p v_0 v_1 =`               |
/// |:-----------------------------------|:----------------------------|
/// | `(v > v'  + 2)        => (p v v')` | `(v_0 > v_1 + 2)`           |
/// | `(v > 0)              => (p 7 v )` | `(v_0 = 7) and (v_1 > 0)`   |
/// | `(v > 0)              => (p 7 v')` | `(v_0 = 7)`                 |
/// | `(v > 0)              => (p v v )` | `(v_0 = v_1) and (v_0 > 0)` |
/// | `(v > 0) and (v <= 0) => (p 7 v')` | `false` (by check-sat)      |
pub struct OneRhs ;

impl OneRhs {
  /// Logs an extraction result.
  fn log_extraction(
    & self, _instance: & Instance,
    _quantfed: & Quantfed, _tterms: & TTermSet
  ) {
    if_log! { @4
      let mut s = "(".to_string() ;

      if ! _quantfed.is_empty() {
        s.push_str("exists") ;
        for (var, sort) in _quantfed {
          s.push_str(
            & format!(" ({} {})", var.default_str(), sort)
          )
        }
        s.push_str(" )\n(")
      }

      s.push_str("and\n") ;

      for (pred, argss) in _tterms.preds() {
        for args in argss {
          s.push_str(
            & format!("  ({} {})\n", _instance[* pred], args)
          )
        }
      }
      for term in _tterms.terms() {
        s.push_str( & format!("  {}\n", term) )
      }

      if ! _quantfed.is_empty() {
        s.push_str(") ")
      }
      s.push_str(")") ;

      log! { @4 "{}", s }
    }
  }


  /// Attemps to unfold a predicate that appears in exactly one RHS.
  ///
  /// Returns `None` if unfolding failed.
  fn work_on(
    & self, pred: PrdIdx, clause: ClsIdx, instance: & mut PreInstance
  ) -> Res< Option<RedInfo> > {

    let extraction_res = {
      let (extraction, instance) = instance.extraction() ;
      let clause = & instance[clause] ;

      if let Some((_this_pred, args)) = clause.rhs() {
        debug_assert_eq!( pred, _this_pred ) ;

        // Does `pred` appear in the lhs?
        match clause.lhs_preds().get(& pred) {
          Some(apps) if ! apps.is_empty() => {
            ExtractRes::SuccessFalse
          },
          _ => extraction.terms_of_rhs_app(
            true, instance, clause.vars(),
            clause.lhs_terms(), clause.lhs_preds(),
            (pred, args)
          ) ?,
        }
      } else {
        bail!("inconsistent instance state")
      }
    } ;

    log! { @4
      "from {}",
      instance.clauses()[clause].to_string_info( instance.preds() ) ?
    }
    log! { @2
      "unfolding {}", conf.emph(& instance[pred].name)
    }

    use self::ExtractRes::* ;
    let info = match extraction_res {
      Trivial => {
        log! { @ 4 "=> trivial" }
        instance.force_false(pred) ?
      },

      SuccessTrue => {
        log! { @ 4 "=> true" }
        instance.force_true(pred) ?
      },
      SuccessFalse => {
        log! { @ 4 "=> false" }
        instance.force_false(pred) ?
      },

      Success( (qvars, tterms) ) => {
        self.log_extraction(
          instance, & qvars, & tterms
        ) ;
        instance.force_pred_left(
          pred, qvars, tterms
        ) ?
      },

      Failed => return Ok(None),
    } ;

    Ok( Some(info) )
  }
}

impl RedStrat for OneRhs {
  fn name(& self) -> & 'static str { "one_rhs" }

  fn new(_: & Instance) -> Self { OneRhs }

  fn apply<'a>(
    & mut self, instance: & mut PreInstance<'a>
  ) -> Res<RedInfo> {
    let mut red_info = RedInfo::new() ;

    'all_preds: for pred in instance.pred_indices() {
      if instance.is_known(pred)
      || instance.clauses_of(pred).1.len() > 1 {
        continue 'all_preds
      }

      conf.check_timeout() ? ;

      let clause = if let Some(clause) = instance.clauses_of(
        pred
      ).1.iter().next().cloned() {
        // Appears in exactly on lhs, let's do this.
        clause
      } else {
        log! {
          @3 "{} does not appear in any rhs, forcing false", instance[pred]
        }
        red_info.preds += 1 ;
        red_info += instance.force_false(pred) ? ;
        continue 'all_preds
      } ;

      log! { @3
        "looking at {} ({}, {})",
        instance[pred],
        instance.clauses_of(pred).0.len(),
        instance.clauses_of(pred).1.len(),
      }

      if let Some(info) = self.work_on(
        pred, clause, instance
      ) ? {
        red_info.preds += 1 ;
        red_info += info ;
        instance.check("after unfolding (one_rhs)") ? ;
        debug_assert! { instance.is_known(pred) }
      } else {
        log! { @4 "failed to unfold {}", instance[pred] }
      }

    }

    Ok( red_info )
  }
}