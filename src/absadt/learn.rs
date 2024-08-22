use super::chc::CEX;
use super::enc::*;
use crate::common::{Cex as Model, *};

pub struct LearnCtx<'a> {
    encs: &'a mut BTreeMap<Typ, Enc>,
    cex: &'a CEX,
    model: &'a Vec<Model>,
}

trait Template {
    fn encode_term(&self, term: &Term) -> Term;
}

struct LinearTemplate {
    n_arg: usize,
    approxs: BTreeMap<String, Approx>,
}

impl LinearTemplate {
    fn new(n_arg: usize) -> Self {
        Self { n_arg }
    }
}

fn get_n_args(enc: &Enc, key: &str) -> usize {
    let approx = enc.approxs.get(key).unwrap();
    let (dtyp, prms) = enc.typ.dtyp_inspect().unwrap();

    dtyp.news.get(&key).unwrap();
}

impl Template for LinearTemplate {
    fn encode_term(&self, term: &Term) -> Term {
        unimplemented!();
    }
}

fn get_templates(n_arg: usize) -> Vec<Box<dyn Template>> {
    vec![Box::new(LinearTemplate::new(n_arg))]
}

impl<'a> LearnCtx<'a> {
    pub fn new(encs: &'a mut BTreeMap<Typ, Enc>, cex: &'a CEX, model: &'a Vec<Model>) -> Self {
        LearnCtx { encs, cex, model }
    }
    pub fn work(&self) -> Res<()> {
        // We now only consider the linear models
        // Appendinx them to the existing encodings
        let mut templates = Vec::new();
        for (idx, enc) in self.encs.values().enumerate() {
            enc.n_params
        }
        Ok(())
    }
}
