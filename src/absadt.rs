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
use hyper_res::ResolutionProof;

use crate::common::*;
use crate::info::{Pred, VarInfo};
use crate::term::Term;
use crate::unsat_core::UnsatRes;
use std::path::PathBuf;

mod exec_chc;
mod hyper_res;
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

fn walk_res(
    instance: &Arc<Instance>,
    n: &hyper_res::Node,
    cur: ClsIdx,
    res: &hyper_res::ResolutionProof,
) -> Res<Term> {
    let c = &instance[cur];
    let (p, args) = c.rhs().ok_or("err")?;
    let name = &instance.preds()[p].name;
    assert_eq!(name, &n.head);

    unimplemented!()
}

/// Obtain a finite expansion of the original CHC instance along with the resolution proof (call-tree).
fn get_cex(instance: &Instance, tree: &CallTree, _profiler: &Profiler) -> Term {
    fn walk(instance: &Instance, tree: &CallTree, cur: &usize) -> Term {
        let cur = tree.nodes.get(cur).unwrap();
        let clause = &instance[cur.clsidx];
        let terms: Vec<_> = clause.lhs_terms().iter().cloned().collect();

        // Assumption: the order of node.children is the same as the order of lhs_preds
        // Correct?
        assert_eq!(clause.lhs_preds().len(), cur.children.len());
        for ((prdidx, args), child) in clause.lhs_preds().iter().zip(cur.children.iter()) {
            println!("{:?}", args);
            let res = walk(instance, tree, child);
            //let t = handle_pred_app(instance, tree, prdidx, args.iter(), res);
            todo!("subst the arguments");
            terms.push(res);
        }
        term::and(terms)
    }

    fn handle_pred_app<'a>(
        instance: &Instance,
        tree: &CallTree,
        prdidx: &PrdIdx,
        args: impl Iterator<Item = Term>,
        child: Term,
    ) -> Term {
        unimplemented!()
    }

    walk(instance, &tree, &tree.root)
}

/*** Pre/Post-process for tracking clauses in the resolution proof ***/

/// Encode each clause with a tag predicate whose name is `tag!X` where `X` is the clause index.
fn encode_tag(instance: &Instance, _profiler: &Profiler) -> Res<Instance> {
    let mut new_instance = instance.clone();
    for (clsidx, _) in instance.clauses().index_iter() {
        let name = format!("tag!{}", clsidx);
        let sig = VarMap::new();
        let prdidx = new_instance.push_pred(name, sig);
        let vars = VarMap::new();
        new_instance.push_new_clause(vars, Vec::new(), Some((prdidx, VarMap::new().into())), "")?;
        new_instance[clsidx].insert_pred_app(prdidx, VarMap::new().into());
    }
    Ok(new_instance)
}

/// Data structure for a node in the call tree
pub struct Node {
    /// Name of the predicate
    pub head: String,
    /// Arguments of the predicate application for refutation
    pub args: Vec<i64>,
    /// Children of this node in the call-tree
    pub children: Vec<usize>,
    /// Index of the clause in the original CHC
    pub clsidx: ClsIdx,
}
impl Node {
    /// Transform hyper_res::Node to Node
    ///
    /// We retrieve the clause index from the encoded-tag predicate.
    /// `cls_map` is a map from node index of the refutation proof to the clause index in the CHC instance.
    fn tr_from_hyper_res(mut n: hyper_res::Node, cls_map: &HashMap<usize, usize>) -> Option<Self> {
        println!("tr_from_hyper_res: {} {:?}", n.head, n.children);
        let idx = n.children.iter().enumerate().find_map(|(i, x)| {
            if cls_map.contains_key(x) {
                Some(i)
            } else {
                None
            }
        })?;
        let cls_id = n.children.remove(idx);
        let clsidx = ClsIdx::new(*cls_map.get(&cls_id)?);

        let args = n
            .arguments
            .into_iter()
            .map(|hyper_res::V::Int(x)| x)
            .collect();
        let node = Self {
            head: n.head.clone(),
            children: n.children.clone(),
            clsidx,
            args,
        };
        Some(node)
    }
}

pub struct CallTree {
    pub root: usize,
    pub nodes: HashMap<usize, Node>,
}
impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}_{}(", self.head, self.clsidx)?;
        let mut itr = self.args.iter();
        if let Some(arg) = itr.next() {
            write!(f, "{}", arg)?;
        }
        for arg in itr {
            write!(f, ", {}", arg)?;
        }
        write!(f, ")")?;
        //write!(f, ") := ")?;
        //for c in self.children.iter() {
        //    write!(f, "{}, ", c)?;
        //}
        Ok(())
    }
}

impl fmt::Display for CallTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut q = vec![(self.root, 0)];
        while let Some((cur, indent)) = q.pop() {
            let n = self.nodes.get(&cur).unwrap();
            for _ in 0..indent {
                write!(f, "  ")?;
            }
            writeln!(f, "{}: {}", cur, n)?;
            for c in n.children.iter().rev() {
                q.push((*c, indent + 1));
            }
        }

        Ok(())
    }
}

/// Transform a resolution proof to a call tree
///
/// 1. Find the tag nodes in the refutation tree
/// 2. Create a map from node id of tag nodes to clause index
/// 3. Transform each node
pub fn decode_tag(res: ResolutionProof) -> Res<CallTree> {
    // map from node (whose head is tag!X) id to its clause index
    let mut map = HashMap::new();
    for n in res.nodes.iter() {
        if n.head.starts_with("tag!") {
            let clsidx = n.head["tag!".len()..]
                .parse::<usize>()
                .map_err(|_| "invalid tag")?;
            let r = map.insert(n.id, clsidx);
            assert!(r.is_none())
        }
    }

    let mut v: Vec<_> = res.get_roots().collect();
    assert!(v.len() == 1);
    let root = v.pop().unwrap().id;

    let mut nodes = HashMap::new();
    for n in res.nodes.into_iter() {
        if n.head.starts_with("tag!") {
            continue;
        }
        let id = n.id;
        let node = Node::tr_from_hyper_res(n, &map).ok_or("hyper resolution is ill-structured")?;
        let r = nodes.insert(id, node);
        assert!(r.is_none())
    }
    Ok(CallTree { root, nodes })
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

    let minus2 = term::cst(val::int(-4));
    let zerot = term::cst(val::int(0));
    let xt = term::var(x, typ::int());
    let x1t = term::add(vec![xt.clone(), term::cst(val::int(1))]);
    let x2t = term::add(vec![xt.clone(), term::cst(val::int(2))]);

    // P(0)
    let mut a1 = VarMap::new();
    a1.push(zerot.clone());
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

    // P(x + 2) => P(x)
    let mut a2 = VarMap::new();
    a2.push(x2t.clone());
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
        "P(x+2) => P(x)",
    )?;

    // P(x) => x <= -2
    let mut a2 = VarMap::new();
    a2.push(xt.clone());
    let t3 = term::TTerm::T(term::lt(xt.clone(), minus2.clone()));
    let t4 = term::TTerm::P {
        pred: p,
        args: a3.into(),
    };
    instance.push_new_clause(vars.clone(), vec![t3, t4], None, "P(x) => x <= 0")?;

    instance.dump_as_smt2(&mut file, "no_def", "").unwrap();

    let encoded_instance = encode_tag(&instance, _profiler)?;

    let rp = match spacer::run_spacer(&encoded_instance)? {
        either::Right(rp) => rp,
        either::Left(_) => {
            panic!("sat")
        }
    };

    let call_tree = decode_tag(rp)?;
    println!("{call_tree}");

    let cex = get_cex(&instance, &call_tree, _profiler);

    unimplemented!();
}
