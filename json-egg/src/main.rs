// Code stolen from:
// https://github.com/mwillsey/egg-herbie-new/blob/8615590ff4ca07703c4b602f7d1b542e6465cfa6/src/main.rs
use egg::{rewrite as rw, *};
use std::{io, sync::mpsc::Receiver};
use std::str::FromStr;
use serde::{Deserialize, Serialize};

// #[derive(Debug)]
// pub struct MatchAST<L> {
//     target: L

// }
// impl<L: Language> CostFunction<L> for MatchAST<L> {
//     type Cost = usize;
//     fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
//     where
//         C: FnMut(Id) -> Self::Cost,
//     {
//         if (enode.eq(&self.target)) { return 1; } else { return 100; }
//     }
//
// }
//

pub type ConstantFold = ();
pub type Constant = num_rational::BigRational;
pub type RecExpr = egg::RecExpr<SymbolLang>;
pub type EGraph = egg::EGraph<SymbolLang, ()>;
pub type Rewrite = egg::Rewrite<SymbolLang, ()>;

pub type IterData = ();
pub type Runner = egg::Runner<SymbolLang, (), IterData>;
pub type Iteration = egg::Iteration<IterData>;

struct SillyCostFn;
impl CostFunction<SymbolLang> for SillyCostFn {
    type Cost = f64;
    fn cost<C>(&mut self, enode: &SymbolLang, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost
    {
        let op_cost = match enode.op.as_str() {
            "ANSWER" => 1.0,
            _ => 100.0
        };
        enode.fold(op_cost, |sum, id| sum + costs(id))
    }
}

#[derive(Debug)]
pub struct AstSizeFive;
impl<L: Language> CostFunction<L> for AstSizeFive {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &L, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> <egg::AstSize as CostFunction<L>>::Cost,
    {
        let tot_size = enode.fold(1, |sum, id| sum + costs(id));
        println!("tot_size: {}",tot_size);
        if tot_size == 5 {1} else {100}
    }
}

#[derive(Deserialize)]
struct RewriteStr {
    name: String,
    lhs: String,
    rhs: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
#[serde(tag = "request")]
enum Request {
    Version,
    LoadRewrites {
        rewrites: Vec<RewriteStr>,
    },
    SimplifyExpressions {
        exprs: Vec<String>,
        #[serde(default = "true_bool")]
        constant_fold: bool,
        #[serde(default = "true_bool")]
        prune: bool,
    },
}

fn true_bool() -> bool {
    true
}

#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
#[serde(tag = "response")]
enum Response {
    Error {
        error: String,
    },
    Version {
        version: String,
    },
    LoadRewrites {
        n: usize,
    },
    SimplifyExpressions {
        iterations: Vec<Iteration>,
        best: Vec<Comparison>,
    },
}

#[derive(Serialize)]
struct Comparison {
    initial_expr: RecExpr,
    initial_cost: usize,
    final_expr: RecExpr,
    final_cost: usize,
}

macro_rules! respond_error {
    ($e:expr) => {
        match $e {
            Ok(ok) => ok,
            Err(error) => return Response::Error { error },
        }
    };
}

struct State {
    rewrites: Vec<Rewrite>,
}

impl Default for State {
    fn default() -> Self { return State { rewrites: Vec::new()  } }
}

fn parse_rewrite(rw: &RewriteStr) -> Result<Rewrite, String> {
    Rewrite::new(
        // rw.name.clone(),
        rw.name.clone(),
        egg::Pattern::from_str(&rw.lhs)
            .map_err(|err| format!("Failed to parse lhs of {}: '{}'\n{}", rw.name, rw.lhs, err))?,
        egg::Pattern::from_str(&rw.rhs)
            .map_err(|err| format!("Failed to parse rhs of {}: '{}'\n{}", rw.name, rw.rhs, err))?,
    )
}

impl State {
    fn handle_request(&mut self, req: Request) -> Response {
        match req {
            Request::Version => Response::Version {
                version: env!("CARGO_PKG_VERSION").into(),
            },
            Request::LoadRewrites { rewrites } => {
                let mut new_rewrites = vec![];
                for rw in rewrites {
                    new_rewrites.push(respond_error!(parse_rewrite(&rw)));
                }
                self.rewrites = new_rewrites;
                Response::LoadRewrites {
                    n: self.rewrites.len(),
                }
            }
            Request::SimplifyExpressions {
                exprs,
                constant_fold,
                prune,
            } => {
                if self.rewrites.is_empty() {
                    return Response::Error {
                        error: "You haven't loaded any rewrites yet!".into(),
                    };
                }

                // let analysis = ConstantFold {
                //     constant_fold,
                //     prune,
                // };
                // let mut runner = Runner::new(analysis).with_node_limit(10_000);
                let mut runner = Runner::new(()).with_node_limit(10_000);
                for expr in exprs {
                    // let e = respond_error!(expr.parse());
                    let eresult : Result<RecExpr, _> = expr.parse();
                    let e : RecExpr = eresult.expect("expected parseable expression");
                    runner = runner.with_expr(&e);
                }

                let initial: Vec<(usize, RecExpr)> = {
                    let mut extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);
                    let find_best = |&id| extractor.find_best(id);
                    runner.roots.iter().map(find_best).collect()
                };

                assert!(self.rewrites.len() > 0);
                runner = runner.run(&self.rewrites);

                let mut extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);
                Response::SimplifyExpressions {
                    iterations: runner.iterations,
                    best: runner
                        .roots
                        .iter()
                        .zip(initial)
                        .map(|(id, (initial_cost, initial_expr))| {
                            let (final_cost, final_expr) = extractor.find_best(*id);
                            Comparison {
                                initial_cost,
                                initial_expr,
                                final_cost,
                                final_expr,
                            }
                        })
                        .collect(),
                }
            }
        }
    }
}

fn mainJson() -> io::Result<()> {
    env_logger::init();
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let deserializer = serde_json::Deserializer::from_reader(stdin.lock());

    let mut state = State::default();

    for read in deserializer.into_iter() {
        let response = match read {
            Err(err) => Response::Error {
                error: format!("Deserialization error: {}", err),
            },
            Ok(req) => state.handle_request(req),
        };
        serde_json::to_writer_pretty(&mut stdout, &response)?;
        println!()
    }

    Ok(())
}


fn mainGroupCheck() {

  let rules: &[Rewrite] = &[
      rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
      rw!("assoc-mul'"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
      rw!("one-mul";  "(* 1 ?a)" => "?a"),
      rw!("one-mul'";  "?a" => "(* 1 ?a)"),
      rw!("inv-left";  "(* (^-1 ?a) ?a)" => "1"),
      rw!("inv-left'";  "1" => "(* (^-1 a) a)"),
      rw!("inv-left''";  "1" => "(* (^-1 b) b)"),
      rw!("mul-one";  "(* ?a 1)" => "?a"),
      rw!("mul-one'";  "?a" => "(* ?a 1)" ),
      rw!("inv-right";  "(* ?a (^-1 ?a))" => "1"),
      rw!("inv-right'";  "1" => "(* a (^-1 a))"),
      rw!("inv-right''";  "1" => "(* b (^-1 b))"),
      //rw!("anwser''";  "(* (^-1 b)(^-1 a))" => "ANSWER"),

  ];

    // We can make our own Language later to work with other types.
    //(a * b) * (1⁻¹⁻¹ * b⁻¹ * ((a⁻¹ * a⁻¹⁻¹⁻¹) * a))
    //let start = "(* (* a b)(* (^-1 (^-1 1))  (* (^-1 b) (* (* (^-1 a) (^-1 (^-1 (^-1 a)))) a))))".parse().unwrap();

    // a * 1  -- won't work without
    //let start = "(* a 1)".parse().unwrap();

    // a⁻¹⁻¹ = a
    let start = "(^-1 (^-1 a))".parse().unwrap();

    //  a⁻¹ * (a * b) = b
    //let start = "(* (^-1  a) (* a b))".parse().unwrap();

    //  a * (a⁻¹ * b) = b
    //let start = "(* a (* (^-1  a) b))".parse().unwrap();

    //(a * b)⁻¹ = b⁻¹ * a⁻¹
    // let start = "(^-1 (* a b))".parse().unwrap();
    //let start = "(* 1 (* 1 1))".parse().unwrap();
    //let start = "(* (^-1 b) (^-1 a))".parse().unwrap();

    //(1 : G)⁻¹ = 1
    //let start = "(^-1 1)".parse().unwrap();

    // That's it! We can run equality saturation now.
    let mut runner = Runner::default()
        //.with_node_limit(105)
        .with_explanations_enabled()
        .with_expr(&start)
        .run(rules);

    // Dump
    // runner.egraph.dot().to_pdf("target/group.pdf").unwrap();
    //runner.egraph.dot().to_pdf("target/group2.pdf").unwrap();
    //println!("Debug: {:?} \n \n", runner.egraph.dump());

    // Extractors can take a user-defined cost function,
    // we'll use the egg-provided AstSize for now
    let mut extractor = Extractor::new(&runner.egraph, AstSize);


    // We want to extract the best expression represented in the
    // same e-class as our initial expression, not from the whole e-graph.
    // Luckily the runner stores the eclass Id where we put the initial expression.
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);


    println!("Best expr : {:?} -- cost: {}",best_expr, best_cost);
    println!("{}", runner.explain_equivalence(&start, &best_expr).get_flat_string());
    // we found the best thing, which is just "a" in this case
}

fn main() {
    // mainJson();
    mainGroupCheck();
}
