mod eld;
mod hoice;
mod spacer;

use crate::absadt::hyper_res;
use crate::common::*;
pub use eld::run_eldarica;
pub use hoice::run_hoice;
pub use spacer::run_spacer;

const CHECK_CHC_TIMEOUT: usize = 60;

pub trait Instance {
    fn dump_as_smt2_with_encode_tag<File, Option>(
        &self,
        w: &mut File,
        options: Option,
        encode_tag: bool,
    ) -> Res<()>
    where
        File: Write,
        Option: AsRef<str>;

    fn dump_as_smt2<W, Options>(&self, w: &mut W, prefix: Options) -> Res<()>
    where
        W: std::io::Write,
        Options: AsRef<str>,
    {
        self.dump_as_smt2_with_encode_tag(w, prefix, true)
    }
}

pub trait CHCSolver {
    fn write_all<S>(&mut self, s: S) -> Res<()>
    where
        S: AsRef<[u8]>;

    fn dump_instance<I>(&mut self, instance: &I) -> Res<()>
    where
        I: Instance,
    {
        self.dump_instance_with_encode_tag(instance, true)
    }

    fn dump_instance_with_encode_tag<I>(&mut self, instance: &I, encode_tag: bool) -> Res<()>
    where
        I: Instance;

    fn check_sat(&mut self) -> Res<bool>;
}

pub fn portfolio<I>(instance: &I) -> Res<either::Either<(), hyper_res::ResolutionProof>>
where
    I: Instance,
{
    let b = run_eldarica(instance, Some(CHECK_CHC_TIMEOUT), false)
        .map_err(|e| log_info!("Eldarica failed with {}", e))
        .unwrap_or(false);
    if b {
        return Ok(either::Left(()));
    }

    run_hoice(instance, Some(CHECK_CHC_TIMEOUT), false).map(|b| {
        if b {
            either::Left(())
        } else {
            either::Right(hyper_res::ResolutionProof::new())
        }
    })
}
