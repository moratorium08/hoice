use crate::common::*;
use crate::unsat_core::UnsatRes;

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
    real_instance: &Arc<Instance>,
    _profiler: &Profiler,
) -> Res<Option<Either<ConjCandidates, UnsatRes>>> {
    println!("hello");
    unimplemented!();
}
