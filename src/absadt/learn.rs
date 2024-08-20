use super::chc::CEX;
use super::enc::*;
use crate::common::{Cex as Model, *};

pub struct LearnCtx<'a> {
    encs: &'a mut BTreeMap<Typ, Enc>,
    cex: &'a CEX,
    model: &'a Vec<Model>,
}

impl<'a> LearnCtx<'a> {
    pub fn new(encs: &'a mut BTreeMap<Typ, Enc>, cex: &'a CEX, model: &'a Vec<Model>) -> Self {
        LearnCtx { encs, cex, model }
    }
    pub fn work(&self) -> Res<()> {
        unimplemented!();
    }
}
