//! Parse resolution proof
//!
//! ## Document
//! - https://github.com/Z3Prover/z3/issues/4863
//! - https://github.com/Z3Prover/z3/blob/0c16d34eb0eb9eb2627606431c631d896d547f6f/src/api/z3_api.h#L748-L785

use crate::common::*;
use lexpr::{from_str, Cons, Value};
use std::collections::HashMap;

type ID = usize;

#[derive(Copy, Clone, Debug)]
pub enum V {
    Int(i64),
}

impl std::fmt::Display for V {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            V::Int(n) => write!(f, "I({})", n),
        }
    }
}

pub struct Node {
    pub id: ID,
    pub head: String,
    pub arguments: Vec<V>,
    pub children: Vec<ID>,
}

impl Node {
    pub fn new(id: ID, head: String, arguments: Vec<V>, children: Vec<ID>) -> Self {
        Self {
            id,
            head,
            arguments,
            children,
        }
    }
}

pub struct ResolutionProof {
    pub nodes: Vec<Node>,
}

impl ResolutionProof {
    pub fn new() -> Self {
        Self { nodes: Vec::new() }
    }
    pub fn get_roots(&self) -> impl Iterator<Item = &Node> {
        self.nodes.iter().filter(|x| x.head.starts_with("query!"))
    }
}

pub struct HyperResolutionParser {
    env: HashMap<String, Value>,
    cache: Vec<(Value, usize)>,
    counter: usize,
}

impl HyperResolutionParser {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
            cache: Vec::new(),
            counter: 0,
        }
    }
    fn get_cache(&self, v: &Value) -> Option<usize> {
        for (k, w) in self.cache.iter() {
            if k == v {
                return Some(*w);
            }
        }
        None
    }
    fn get_new_counter(&mut self) -> usize {
        let c = self.counter;
        self.counter += 1;
        c
    }
    fn parse_defs(&mut self, expr: &Value) -> Res<()> {
        let cons = expr.as_cons().ok_or("invalid defs")?;
        for c in cons.iter() {
            let mut c = c.car().as_cons().ok_or("invalid def")?.iter();
            let var = c.next().ok_or("invalid def")?.car();
            let var = var.as_symbol().ok_or("invalid def")?;
            let val = c.next().ok_or("invalid def")?.car();
            self.env.insert(var.to_string(), val.clone());
        }
        Ok(())
    }
    fn parse_let(&mut self, expr: &Value) -> Res<(usize, ResolutionProof)> {
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
    fn parse_mp(&mut self, expr: &Value) -> Res<(usize, ResolutionProof)> {
        let c = match expr {
            Value::Cons(c) => c,
            _ => bail!("invalid mp"),
        };
        let mut c = c.iter();
        let child = c.next().ok_or("invalid mp")?.car();
        let _asserted = c.next().ok_or("invalid mp")?.car();
        let _false_e = c.next().ok_or("invalid mp")?.car();
        if c.next().is_some() {
            bail!("invalid mp");
        }
        let (i, proofs) = self.parse_expr(child)?;
        Ok((i, proofs))
    }
    fn parse_hyper_res(&mut self, expr: &Value) -> Res<(usize, ResolutionProof)> {
        let c = match expr {
            Value::Cons(c) => c,
            _ => bail!("invalid hyper-res"),
        };
        let mut c = c.iter();
        let asserted = c.next().ok_or("invalid hyper-res")?;
        let _ = self.parse_asserted(asserted.car())?;
        let mut v: Vec<_> = c.collect();
        let head = v.pop().ok_or("invalid hyper-res")?.car();
        if let Some(e) = self.get_cache(head) {
            return Ok((e, ResolutionProof::new()));
        }
        let i = self.get_new_counter();
        let mut children = vec![];
        for x in v.into_iter() {
            let x = x.car();
            let r = self.parse_expr(x)?;
            children.push(r);
        }
        let (indices, proofs): (Vec<_>, Vec<_>) = children.into_iter().unzip();
        self.cache.push((head.clone(), i));
        let mut proofs: Vec<_> = proofs.into_iter().map(|x| x.nodes).flatten().collect();
        let (head, arguments) = self.parse_head(head)?;
        proofs.push(Node::new(i, head, arguments, indices));
        let resolution_proof = ResolutionProof { nodes: proofs };
        Ok((i, resolution_proof))
    }
    fn parse_val(&mut self, val: &Value) -> Res<V> {
        match val {
            Value::Number(n) => Ok(V::Int(n.as_i64().ok_or("invalid int")?)),
            Value::Cons(c) => {
                let mut c = c.iter();
                let top = c.next().ok_or("invalid val")?.car();
                let pred = top.as_symbol().ok_or("invalid val")?;
                if pred != "-" {
                    bail!("invalid val: {}", val);
                }
                let arg = c.next().ok_or("invalid val")?.car();
                let arg = arg.as_i64().ok_or("invalid val")?;
                if c.next().is_some() {
                    bail!("invalid val: {}", val);
                }
                Ok(V::Int(-arg))
            }
            _ => bail!("invalid argument of head: {}", val),
        }
    }
    fn parse_head(&mut self, head: &Value) -> Res<(String, Vec<V>)> {
        match head {
            Value::Cons(cons) => {
                let mut cons_iter = cons.iter();
                let top = cons_iter.next().ok_or("invalid head")?.car();
                let pred = top.as_symbol().ok_or("invalid head")?;
                let arguments: Result<Vec<_>, _> =
                    cons_iter.map(|x| self.parse_val(x.car())).collect();
                Ok((pred.to_string(), arguments?))
            }
            Value::Symbol(s) => {
                let pred = s.to_string();
                Ok((pred, vec![]))
            }
            _ => bail!("invalid head"),
        }
    }
    fn parse_asserted(&mut self, _expr: &Value) -> Res<()> {
        Ok(())
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
    fn parse_expr(&mut self, expr: &Value) -> Res<(usize, ResolutionProof)> {
        use Value::*;
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
                    //Symbol(s) if s.as_ref() == "asserted" => self.parse_asserted(cont),
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
                    let v = v.clone();
                    self.parse_expr(&v)
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
        let (_, p) = match from_str(text.as_ref()) {
            Ok(v) => self.parse_expr(&v)?,
            Err(e) => bail!("parse error: {}", e),
        };
        // for x in p.iter() {
        //     print!("{}, {}(", x.id, x.head);
        //     for y in x.arguments.iter() {
        //         print!("{},", y);
        //     }
        //     print!("): ");

        //     for y in x.children.iter() {
        //         print!(" {}", y);
        //     }
        //     println!()
        // }
        Ok(p)
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

#[test]
fn test_parse2() {
    let s = "(let ((a!1 (forall ((A Int))
             (! (=> (and tag!2 (P A) (>= A 1)) (query!0 A)) :weight 0)))
      (a!2 (forall ((A Int) (B Int))
             (! (=> (and tag!0 (= A (+ 1 B))) (P A)) :weight 0))))
(let ((a!3 ((_ hyper-res 0 0 0 1 0 2)
             (asserted a!1)
             ((_ hyper-res 0 0) (asserted tag!2) tag!2)
             ((_ hyper-res 0 0 0 1)
               (asserted a!2)
               ((_ hyper-res 0 0) (asserted tag!0) tag!0)
               (P 1))
             (query!0 1))))
  (mp a!3 (asserted (=> (query!0 1) false)) false)))";
    let mut parser = HyperResolutionParser::new();
    parser.parse_spacer(s).unwrap();
    println!("{}", s);
}
