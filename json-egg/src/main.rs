// Code stolen from:
// https://github.com/mwillsey/egg-herbie-new/blob/8615590ff4ca07703c4b602f7d1b542e6465cfa6/src/main.rs
use egg::{rewrite as rw, *};
// use std::f32::consts::E;
use std::{io};
// use std::{sync::mpsc::Receiver};
use std::str::FromStr;
use serde::{Deserialize, Serialize};
use egg::SymbolLang;
use egg::Explanation;

pub type ConstantFold = ();
pub type Constant = num_rational::BigRational;
pub type RecExpr = egg::RecExpr<SymbolLang>;
pub type EGraph = egg::EGraph<SymbolLang, ()>;
pub type Rewrite = egg::Rewrite<SymbolLang, ()>;

pub type IterData = ();
pub type Runner = egg::Runner<SymbolLang, (), IterData>;
pub type Iteration = egg::Iteration<IterData>;


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
    #[serde(rename_all = "kebab-case")]
    PerformRewrite {
        rewrites: Vec<RewriteStr>,
        target_lhs: String,
        target_rhs: String,
    }
}


#[derive(Serialize)]
#[serde(rename_all = "kebab-case")]
#[serde(tag = "response")]
enum Response {
    PerformRewrite {
        success: bool,
        // TODO: how does one use Sexp?
        explanation: Vec<String>
    },
    Error { error: String }
}

macro_rules! respond_error {
    ($e:expr) => {
        match $e {
            Ok(ok) => ok,
            Err(error) => return Response::Error { error : error.to_string() },
        }
    };
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


fn handle_request(req: Request) -> Response {
    match req {
        Request::PerformRewrite { rewrites, target_lhs, target_rhs } => {
            let mut new_rewrites = vec![];
            for rw in rewrites {
                new_rewrites.push(respond_error!(parse_rewrite(&rw)));
            }
            // let targetLhsExpr : Result<RecExpr, _> = respond_error!(targetLhs.parse());
            // let e : RecExpr = eresult.expect("expected parseable expression");
            let target_lhs_expr : RecExpr  = respond_error!(target_lhs.parse());
            let target_rhs_expr : RecExpr  = respond_error!(target_rhs.parse());
            let mut graph : EGraph = EGraph::new(()).with_explanations_enabled();

            let lhs_id = graph.add_expr(&target_lhs_expr);
            let rhs_id = graph.add_expr(&target_rhs_expr);
            // let e : RecExpr = eresult.expect("expected parseable expression");
            let mut runner = Runner::default()
            .with_egraph(graph)
            //.with_node_limit(105)
            .with_explanations_enabled()
            .run(&new_rewrites);

            if runner.egraph.find(lhs_id) ==  runner.egraph.find(rhs_id) {
                let mut explanation : Explanation<SymbolLang> = runner.explain_equivalence(&target_lhs_expr,
                    & target_rhs_expr);
                let flat_strings = explanation.get_flat_strings();
                Response::PerformRewrite { success: true, explanation: flat_strings }
            } else {
                Response::PerformRewrite { success: false, explanation: vec![] }

            }
        }
    }
}


fn main_json() -> io::Result<()> {
    env_logger::init();
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    let deserializer = serde_json::Deserializer::from_reader(stdin.lock());


    for read in deserializer.into_iter() {
        let response = match read {
            Err(err) => Response::Error {
                error: format!("Deserialization error: {}", err),
            },
            Ok(req) => handle_request(req),
        };
        serde_json::to_writer_pretty(&mut stdout, &response)?;
        println!()
    }

    Ok(())
}


fn main_group_check() {

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
    let extractor = Extractor::new(&runner.egraph, AstSize);


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
    main_json().unwrap();
    // main_group_check();

}
