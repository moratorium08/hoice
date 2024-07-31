//! Parse resolution proof
//!
//! ## Document
//! - https://github.com/Z3Prover/z3/issues/4863
//! - https://github.com/Z3Prover/z3/blob/0c16d34eb0eb9eb2627606431c631d896d547f6f/src/api/z3_api.h#L748-L785

use crate::common::*;
use lexpr::{from_str, Cons, Value};
use std::collections::HashMap;

type ID = usize;

pub struct Node {
    id: VarIdx,
    head: term::Term,
    children: Vec<VarIdx>,
}

pub struct Graph {
    nodes: VarMap<Node>,
}

impl Graph {
    pub fn new() -> Self {
        Self {
            nodes: VarMap::new(),
        }
    }
}

type ResolutionProof = Box<Node>;

pub struct HyperResolutionParser<'a> {
    env: HashMap<&'a str, &'a Value>,
}

impl<'a> HyperResolutionParser<'a> {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
        }
    }
    fn parse_defs(&mut self, expr: &Value) -> Res<()> {
        let cons = match expr {
            Value::Cons(c) => c,
            _ => bail!("invalid let"),
        };
        for c in cons.iter() {
            println!("{:#?}", c);
        }
        Ok(())
    }
    fn parse_let(&mut self, expr: &Value) -> Res<ResolutionProof> {
        match expr {
            Value::Cons(c) => {
                let old = self.env.clone();
                let defs = c.car();
                let cont = c.cdr();
                self.parse_defs(defs)?;
                let h = cont.as_cons();
                if let Some(h) = h {
                    if !h.cdr().is_null() {
                        bail!("invalid let: {} must be null", h.cdr());
                    }
                    let h = h.car();
                    let r = self.parse_expr(h)?;
                    self.env = old;
                    Ok(r)
                } else {
                    bail!("invalid let: ")
                }
            }
            _ => bail!("invalid let"),
        }
    }
    fn parse_mp(&mut self, expr: &Value) -> Res<ResolutionProof> {
        let c = match expr {
            Value::Cons(c) => c,
            _ => bail!("invalid mp"),
        };
        let mut c = c.iter();
        let child = c.next().ok_or("invalid mp")?.car();
        let asserted = c.next().ok_or("invalid mp")?.car();
        let false_e = c.next().ok_or("invalid mp")?.car();
        if c.next().is_some() {
            bail!("invalid mp");
        }
        let t = self.parse_expr(child)?;
        unimplemented!()
    }
    fn parse_hyper_res(&mut self, expr: &Value) -> Res<ResolutionProof> {
        let c = match expr {
            Value::Cons(c) => c,
            _ => bail!("invalid hyper-res"),
        };
        let mut c = c.iter();
        let mut children = vec![];
        for x in c {
            let x = x.car();
            let r = self.parse_expr(x)?;
            children.push(r);
        }
        unimplemented!()
    }
    fn parse_asserted(&mut self, expr: &Value) -> Res<ResolutionProof> {
        let c = match expr {
            Value::Cons(c) => c,
            _ => bail!("invalid asserted"),
        };
        let mut c = c.iter();
        let child = c.next().ok_or("invalid asserted")?.car();
        if c.next().is_some() {
            bail!("invalid asserted");
        }
        let t = self.parse_expr(child)?;
        unimplemented!()
    }
    fn as_hyper_res(&self, c: &Cons) -> Option<Vec<i64>> {
        let mut c = c.iter();
        let n = c.next()?.car();
        if n.as_symbol()? != "_" {
            return None;
        }

        let n = c.next()?.car();
        if n.as_symbol()? != "hyper-res" {
            return None;
        }

        let res = c.flat_map(|x| x.car().as_i64()).collect();
        Some(res)
    }
    fn parse_expr(&mut self, expr: &Value) -> Res<ResolutionProof> {
        use Value::*;
        println!("parse_expr: {}", expr);
        match expr {
            Cons(c) => {
                let h = c.car();
                let cont = c.cdr();
                match h {
                    Nil => todo!(),
                    Null => todo!(),
                    Bool(_) => todo!(),
                    Number(_) => todo!(),
                    Char(_) => todo!(),
                    String(_) => todo!(),
                    Symbol(s) if s.as_ref() == "let" => self.parse_let(cont),
                    Symbol(s) if s.as_ref() == "mp" => self.parse_mp(cont),
                    Symbol(s) if s.as_ref() == "asserted" => self.parse_asserted(cont),
                    Symbol(_) => todo!(),
                    Keyword(_) => todo!(),
                    Bytes(_) => todo!(),
                    Cons(c) => match self.as_hyper_res(c) {
                        Some(_) => self.parse_hyper_res(cont),
                        None => bail!("invalid expr: {}", expr),
                    },
                    Vector(_) => todo!(),
                }
            }
            Nil => todo!(),
            Null => todo!(),
            Bool(_) => todo!(),
            Number(_) => todo!(),
            Char(_) => todo!(),
            String(_) => todo!(),
            Symbol(s) => {
                if let Some(v) = self.env.get(s.as_ref()) {
                    self.parse_expr(v)
                } else {
                    bail!("undefined symbol: {}", s)
                }
            }
            Keyword(_) => todo!(),
            Bytes(_) => todo!(),
            Vector(_) => todo!(),
        }
    }
    pub fn parse_spacer<S>(&mut self, text: S) -> Res<ResolutionProof>
    where
        S: AsRef<str>,
    {
        let text = text.as_ref();
        match from_str(text) {
            Ok(v) => self.parse_expr(&v),
            Err(e) => bail!("parse error: {}", e),
        }
    }
}

#[test]
fn test_parse() {
    let s = " (let ((a!1 (forall ((A Int))
             (! (=> (and (P A) (>= A 1)) (query!0 A)) :weight 0)))
      (a!2 (forall ((A Int) (B Int)) (! (=> (= A (+ 1 B)) (P A)) :weight 0))))
  (mp ((_ hyper-res 0 0 0 1)
        (asserted a!1)
        ((_ hyper-res 0 0) (asserted a!2) (P 1))
        (query!0 1))
      (asserted (=> (query!0 1) false))
      false))";
    let mut parser = HyperResolutionParser::new();
    parser.parse_spacer(s).unwrap();
    println!("{}", s);
}
