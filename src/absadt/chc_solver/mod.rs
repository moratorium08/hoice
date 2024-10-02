mod eld;
mod spacer;

use crate::common::*;
pub use eld::run_eldarica;
pub use spacer::run_spacer;

pub trait Instance {
    fn dump_as_smt2<W, Options>(&self, w: &mut W, prefix: Options) -> Res<()>
    where
        W: std::io::Write,
        Options: AsRef<str>;
}

pub trait CHCSolver {
    fn write_all<S>(&mut self, s: S) -> Res<()>
    where
        S: AsRef<[u8]>;

    fn dump_instance<I>(&mut self, instance: &I) -> Res<()>
    where
        I: Instance;

    fn check_sat(&mut self) -> Res<bool>;
}
