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
use crate::common::*;
use crate::info::{Pred, VarInfo};
use crate::unsat_core::UnsatRes;
use std::path::PathBuf;

mod exec_chc;
mod spacer;

pub struct AbsADTConf {
    /// Original CHC Instance over LIA + ADT
    instance: Arc<Instance>,
    log_dir: PathBuf,
    encs: BTreeMap<Typ, Enc>,
}

pub struct Approx {
    /// Definition of the arguments
    pub args: VarInfos,
    /// n terms for approximation
    pub terms: Vec<Term>,
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

impl AbsADTConf {
    /// Initialize some confirugation such as making logdir
    fn new(instance: &Arc<Instance>) -> Res<Self> {
        let mut log_dir = crate::common::conf.out_dir(instance);
        log_dir.push("absadt");
        mk_dir(&log_dir)?;

        let instance = instance.clone();
        Ok(AbsADTConf {
            instance,
            log_dir,
            encs: BTreeMap::new(),
        })
    }

    fn instance_log_files<S: AsRef<str>>(&self, name: S) -> Res<::std::fs::File> {
        use std::fs::OpenOptions;
        let mut path = self.log_dir.clone();
        path.push(name.as_ref());
        path.set_extension("smt2");
        let file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(&path)
            .chain_err(|| {
                format!(
                    "while creating instance dump file {}",
                    path.to_string_lossy()
                )
            })?;
        Ok(file)
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
    println!("hello");
    let cls = instance.clauses();
    let c = cls.iter().next().unwrap();

    let adtconf = AbsADTConf::new(instance)?;
    let mut file = adtconf.instance_log_files("hoge")?;

    instance.dump_as_smt2(&mut file, "hoge", "").unwrap();

    // ~~~playground~~~
    let decs = dtyp::get_all();
    assert!(!decs.is_empty(), "no ADT is defined");

    // dtype name: Lst
    // RDTyp {
    //     name: "Lst",
    //     deps: [],
    //     prms: TPrmMap {
    //         vec: [
    //             "T",
    //         ],
    //     },
    //     news: {
    //         "cons": [
    //             (
    //                 "head",
    //                 Param(
    //                     TPrmIdx {
    //                         val: 0,
    //                     },
    //                 ),
    //             ),
    //             (
    //                 "tail",
    //                 DTyp(
    //                     "Lst",
    //                     Pos(
    //                         79,
    //                     ),
    //                     TPrmMap {
    //                         vec: [
    //                             Param(
    //                                 TPrmIdx {
    //                                     val: 0,
    //                                 },
    //                             ),
    //                         ],
    //                     },
    //                 ),
    //             ),
    //         ],
    //         "nil": [],
    //     },
    //     default: "nil",
    // }
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

    // generate a new instance
    // P(0)
    // P(x + 1) => P(x)
    // P(x) => x <= 0

    let mut instance = Instance::new();

    let mut vars = VarInfos::new();
    let x = vars.next_index();
    let info = VarInfo::new("x", typ::int(), x);
    vars.push(info);

    let mut sig = VarMap::new();
    sig.push(typ::int());

    let p = instance.push_pred("P", sig);

    let zerot = term::cst(val::int(0));
    let xt = term::var(x, typ::int());
    let x1t = term::add(vec![xt.clone(), term::cst(val::int(1))]);

    // P(0)
    let mut a1 = VarMap::new();
    a1.push(x1t.clone());
    instance.push_new_clause(vars.clone(), vec![], Some((p, a1.into())), "P(0)")?;

    // P(x + 1) => P(x)
    let mut a2 = VarMap::new();
    a2.push(x1t.clone());
    let t1 = term::TTerm::P {
        pred: p,
        args: a2.into(),
    };

    let mut a3 = VarMap::new();
    a3.push(xt.clone());
    instance.push_new_clause(
        vars.clone(),
        vec![t1.into()],
        Some((p, a3.clone().into())),
        "P(x+1) => P(x)",
    )?;

    // P(x) => x <= 0
    let mut a2 = VarMap::new();
    a2.push(xt.clone());
    let t3 = term::TTerm::T(term::gt(xt.clone(), zerot.clone()));
    let t4 = term::TTerm::P {
        pred: p,
        args: a3.into(),
    };
    instance.push_new_clause(vars.clone(), vec![t3, t4], None, "P(x) => x <= 0")?;

    instance.dump_as_smt2(&mut file, "no_def", "").unwrap();

    spacer::run_spacer(&instance)?;
    unimplemented!();
}
