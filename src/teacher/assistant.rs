//! Handles example propagation.

use common::*;
use data::{Data, Sample};

/// Result of trying to force a sample positive/negative.
pub enum ForceRes {
    /// Failure.
    None,
    /// Sample was classified as positive.
    Pos { sample: Sample, clause: ClsIdx },
    /// Sample was classified as negative.
    Neg { sample: Sample, clause: ClsIdx },
}

/// Stores data from a positive / strict negative clause.
///
/// # Examples
///
/// If the clause is `forall x, y | x > 0 => p(x + 1, y)` then the data stored is
///
/// |      |                          |
/// |:----:|:-------------------------|
/// | conj | `x > 0`                  |
/// | args | `v_0 -> x + 1, v_1 -> y` |
/// | vars | `v_0`                    |
#[derive(Clone, Debug)]
pub struct ClauseData {
    /// Index of the clause.
    pub idx: ClsIdx,
    /// Conjunction of lhs terms.
    pub conj: Term,
    /// Map from the clause's **only** predicate to the clause's variables.
    pub args: VarTerms,
    /// Variables of the predicate that are relevant w.r.t. `conj`. None if all are relevant.
    pub vars: Option<VarSet>,
    /// True if the clause is a positive one.
    pub pos: bool,
}
impl ClauseData {
    /// Constructor.
    pub fn new(idx: ClsIdx, pos: bool, args: &VarTerms, lhs_terms: &TermSet) -> Self {
        let conj = term::and(lhs_terms.iter().cloned().collect());
        let args = args.clone();
        let conj_vars = term::vars(&conj);

        let mut vars = VarSet::new();
        for (pred_var, arg) in args.index_iter() {
            if let Some(var) = arg.var_idx() {
                if !conj_vars.contains(&var) {
                    continue;
                }
            }
            let is_new = vars.insert(pred_var);
            debug_assert! { is_new }
        }
        let vars = if vars.len() == args.len() {
            None
        } else {
            Some(vars)
        };

        ClauseData {
            idx,
            conj,
            args,
            vars,
            pos,
        }
    }
}

/// Propagates examples, tries to break implication constraints.
pub struct Assistant {
    /// Core, to communicate with the teacher.
    // core: & 'a MsgCore,
    /// Solver.
    solver: Solver<()>,
    /// Instance.
    instance: Arc<Instance>,
    /// Profiler.
    _profiler: Profiler,
    /// True if we're using ADTs.
    using_adts: bool,
    /// Maps predicates to their positive / strict negative clause data.
    clauses: PrdHMap<Vec<ClauseData>>,
}

impl Assistant {
    /// Constructor.
    pub fn new(instance: Arc<Instance>) -> Res<Self> {
        let solver = conf.solver.spawn("assistant", (), &instance)?;
        let _profiler = Profiler::new();

        let using_adts = dtyp::get_all().iter().next().is_some();

        let clauses = PrdHMap::new();

        let mut res = Assistant {
            // core,
            solver,
            instance,
            _profiler,
            using_adts,
            clauses,
        };

        res.register_clauses()?;

        Ok(res)
    }

    /// Registers all positive / strict negative clauses.
    fn register_clauses(&mut self) -> Res<()> {
        let instance = self.instance.clone();
        for clause_idx in instance.pos_clauses() {
            let clause = &instance[*clause_idx];

            debug_assert! { clause.lhs_preds().is_empty() }

            if let Some((pred, args)) = clause.rhs() {
                self.register(*clause_idx, pred, args, clause.lhs_terms(), true)
            } else {
                bail!("inconsistent positive clause set from instance")
            }
        }

        for clause_idx in instance.strict_neg_clauses() {
            let clause = &instance[*clause_idx];

            debug_assert! { clause.rhs().is_none() }
            debug_assert! { clause.lhs_preds().len() == 1 }

            if let Some((pred, argss)) = clause.lhs_preds().iter().next() {
                debug_assert! { argss.len() == 1 }

                if let Some(args) = argss.iter().next() {
                    self.register(*clause_idx, *pred, args, clause.lhs_terms(), false)
                } else {
                    bail!("inconsistent clause state")
                }
            } else {
                bail!("inconsistent strict negative clause set from instance")
            }
        }

        Ok(())
    }

    /// Registers some clause data for a predicate.
    ///
    /// Boolean flag indicates whether the original clause is positive or not.
    fn register(
        &mut self,
        idx: ClsIdx,
        pred: PrdIdx,
        args: &VarTerms,
        lhs_terms: &TermSet,
        pos: bool,
    ) {
        let data = ClauseData::new(idx, pos, args, lhs_terms);
        self.clauses.entry(pred).or_insert_with(Vec::new).push(data)
    }

    /// Destroys the assistant.
    pub fn finalize(mut self) -> Res<Profiler> {
        self.solver.kill().chain_err(|| "While killing solver")?;
        Ok(self._profiler)
    }

    /// Breaks implications.
    pub fn break_implications(&mut self, data: &mut Data) -> Res<()> {
        if data.constraints.is_empty() {
            return Ok(());
        }

        let (mut pos, mut neg) = (Vec::new(), Vec::new());
        // msg! { debug self.core => "breaking implications..." }
        profile! { self "constraints received" => add data.constraints.len() }

        'all_constraints: for cstr in CstrRange::zero_to(data.constraints.len()) {
            // Can happen because of simplifications when propagating.
            if cstr > data.constraints.len() {
                break;
            }
            if data.constraints[cstr].is_tautology() {
                continue;
            }

            // debug! {
            //   "  {}", data.constraints[cstr].string_do(
            //     self.instance.preds(), |s| s.to_string()
            //   ).unwrap()
            // }

            let mut trivial = false;
            let mut rhs_false = false;
            let mut lhs_unknown = 0;
            macro_rules! move_on {
                (if trivial) => {
                    if trivial {
                        move_on!()
                    }
                };
                () => {{
                    if trivial || lhs_unknown == 0 || rhs_false && lhs_unknown == 1 {
                        profile! { self "constraints   broken" => add 1 }
                    }

                    // Discard the constraint, regardless of what will happen.
                    profile! { self tick "data" }
                    data.tautologize(cstr)?;
                    for (Sample { pred, args }, clause) in pos.drain(0..) {
                        data.add_pos(clause, pred, args);
                    }
                    for (Sample { pred, args }, clause) in neg.drain(0..) {
                        data.add_neg(clause, pred, args);
                    }
                    data.propagate()?;
                    profile! { self mark "data" }
                    continue 'all_constraints;
                }};
            }

            if let Some(&Sample { pred, ref args }) = data.constraints[cstr].rhs() {
                match self.try_force(data, pred, args)? {
                    ForceRes::None => (),
                    ForceRes::Pos { sample, clause } => {
                        pos.push((sample, clause));
                        // Constraint is trivial, move on.
                        trivial = true
                    }
                    ForceRes::Neg { sample, clause } => {
                        rhs_false = true;
                        neg.push((sample, clause))
                    }
                }
            }

            // move_on!(if trivial) ;

            if let Some(lhs) = data.constraints[cstr].lhs() {
                for (pred, samples) in lhs {
                    let mut lhs_trivial = true;
                    for sample in samples {
                        match self.try_force(data, *pred, sample)? {
                            ForceRes::None => {
                                lhs_unknown += 1;
                                lhs_trivial = false
                            }
                            ForceRes::Pos { sample, clause } => pos.push((sample, clause)),
                            ForceRes::Neg { sample, clause } => {
                                neg.push((sample, clause));
                                trivial = true;
                                // Constraint is trivial, move on.
                                // break 'lhs
                            }
                        }
                    }
                    trivial = trivial || lhs_trivial
                }
            } else {
                bail!("Illegal constraint")
            }

            move_on!()
        }

        let (_pos_count, _neg_count) = data.pos_neg_count();
        if !data.pos.is_empty() {
            profile! { self "positive examples generated" => add _pos_count }
        }
        if !data.neg.is_empty() {
            profile! { self "negative examples generated" => add _neg_count }
        }

        Ok(())
    }

    /// Checks if a sample can be forced to anything.
    ///
    /// If it can't, return None. If it can, returns
    ///
    /// - `ForceRes::Pos` of a sample which, when forced positive, will force the
    ///   input sample to be classified positive.
    /// - `ForceRes::Neg` of a sample which, when forced negative, will force the
    ///   input sample to be classified negative.
    pub fn try_force(&mut self, _data: &Data, pred: PrdIdx, vals: &VarVals) -> Res<ForceRes> {
        let clause_data = if let Some(data) = self.clauses.get(&pred) {
            data
        } else {
            return Ok(ForceRes::None);
        };

        self.solver.comment_args(format_args!(
            "working on sample ({} {})",
            self.instance[pred], vals
        ))?;

        macro_rules! solver {
            (push) => {
                if !self.using_adts {
                    self.solver.push(1)?
                }
            };
            (pop) => {
                if self.using_adts {
                    smt::reset(&mut self.solver, &self.instance)?
                } else {
                    self.solver.pop(1)?
                }
            };
        }

        for ClauseData {
            idx,
            conj,
            args,
            vars,
            pos,
        } in clause_data
        {
            self.solver.comment_args(format_args!(
                "working on positive clauses with lhs {}",
                conj
            ))?;

            let clause = *idx;

            solver!(push);

            self.instance[clause].declare(&mut self.solver)?;

            self.solver.assert(&smt::SmtTerm::new(conj))?;
            self.solver
                .assert(&ArgValEq::new(args, vals, vars.as_ref()))?;

            let sat = profile! {
                self wrap { self.solver.check_sat() } "smt"
            }?;

            solver!(pop);

            if sat {
                let args = if let Some(vars) = vars {
                    let mut nu_vals = var_to::vals::RVarVals::with_capacity(vals.len());
                    for (idx, val) in vals.index_iter() {
                        if vars.contains(&idx) {
                            nu_vals.push(val.clone())
                        } else {
                            nu_vals.push(val::none(val.typ()))
                        }
                    }
                    var_to::vals::new(nu_vals)
                } else {
                    vals.clone()
                };

                self.solver.comment_args(format_args!(
                    "success, yielding {} sample ({} {})",
                    if *pos { "positive" } else { "negative" },
                    self.instance[pred],
                    args
                ))?;

                let sample = Sample { pred, args };

                if *pos {
                    return Ok(ForceRes::Pos { sample, clause });
                } else {
                    return Ok(ForceRes::Neg { sample, clause });
                }
            }
        }

        Ok(ForceRes::None)
    }
}

/// Wrapper around some arguments and some values.
///
/// Used to assert `(= arg[i] val[i])`.
pub struct ArgValEq<'a> {
    /// Arguments.
    args: &'a VarTerms,
    /// Values.
    vals: &'a VarVals,
    /// Only assert equalities for variables that are in this set. Assert all if none.
    vars: Option<&'a VarSet>,
}
impl<'a> ArgValEq<'a> {
    /// Constructor.
    pub fn new(args: &'a VarTerms, vals: &'a VarVals, vars: Option<&'a VarSet>) -> Self {
        debug_assert_eq! { args.len(), vals.len() }
        ArgValEq { args, vals, vars }
    }
}
impl<'a> Expr2Smt<()> for ArgValEq<'a> {
    fn expr_to_smt2<Writer>(&self, w: &mut Writer, _: ()) -> ::rsmt2::SmtRes<()>
    where
        Writer: Write,
    {
        write!(w, "(and")?;
        let mut skipped = 0;

        for ((var, arg), val) in self.args.index_iter().zip(self.vals.iter()) {
            // Skip if variable has no value, or the set of variables to assert does not contain
            // it.
            if !val.is_known() || self.vars.map(|set| !set.contains(&var)).unwrap_or(false) {
                skipped += 1;
                continue;
            }

            match val.get() {
                val::RVal::B(b) => {
                    write!(w, " ")?;
                    if !b {
                        write!(w, "(not ")?
                    }
                    arg.write(w, |w, v| w.write_all(v.default_str().as_bytes()))?;
                    if !b {
                        write!(w, ")")?
                    }
                }

                val::RVal::I(ref i) => {
                    write!(w, " (= ")?;
                    arg.write(w, |w, v| w.write_all(v.default_str().as_bytes()))?;
                    write!(w, " ")?;
                    int_to_smt!(w, i)?;
                    write!(w, ")")?
                }

                val::RVal::R(ref r) => {
                    write!(w, " (= ")?;
                    arg.write(w, |w, v| w.write_all(v.default_str().as_bytes()))?;
                    write!(w, " ")?;
                    rat_to_smt!(w, r)?;
                    write!(w, ")")?
                }

                val::RVal::Array { .. } | val::RVal::DTypNew { .. } => {
                    write!(w, " (= ")?;
                    arg.write(w, |w, v| w.write_all(v.default_str().as_bytes()))?;
                    write!(w, " {})", val)?
                }

                val::RVal::N(_) => (),
            }
        }

        if skipped == self.args.len() {
            write!(w, " true")?
        }
        write!(w, ")")?;
        Ok(())
    }
}
