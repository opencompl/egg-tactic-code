// Code stolen from:
// https://github.com/mwillsey/egg-herbie-new/blob/8615590ff4ca07703c4b602f7d1b542e6465cfa6/src/main.rs
use egg::{rewrite as rw, *};
//use std::arch::x86_64::m128Ext;
use std::borrow::Borrow;
use std::rc::Rc;
use std::collections::HashMap;
// use std::f32::consts::E;
use std::{io};
use symbolic_expressions::Sexp;
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
pub type FlatTerm = egg::FlatTerm<SymbolLang>;
pub type PatternAst = egg::PatternAst<SymbolLang>;
pub type FlatExplanation = egg::FlatExplanation<SymbolLang>;
pub type ENodeOrVar = egg::ENodeOrVar<SymbolLang>;
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

#[derive(Deserialize, Debug)]
struct RewriteStr {
    name: String,
    lhs: String,
    rhs: String,
}

#[derive(Deserialize, Debug)]
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

#[derive(Serialize,Debug)]
#[serde(rename_all = "kebab-case")]
pub struct LeanRewriteInfo {
    rewrite: String, // name of the rewrite
    args: HashMap<String, String>, // metavariable values.
    direction: String, // direction of the rewrite

}


#[derive(Serialize,Debug)]
#[serde(rename_all = "kebab-case")]
#[serde(tag = "response")]
enum Response {
    PerformRewrite {
        success: bool,
        // TODO: how does one use Sexp?
        explanation: Vec<LeanRewriteInfo>
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


fn flat_term_to_raw_sexp(t: &FlatTerm) -> Sexp {
    let op = Sexp::String(t.node.to_string());
    let mut expr = if t.node.is_leaf() {
        op
    } else {
        let mut vec = vec![op];
        for child in &t.children {
            vec.push(child.get_sexp());
        }
        Sexp::List(vec)
    };

    expr
}



// Extract the rule as forward/backward from the flat term.
// This is used to run the rules from our Lean engine.
fn flat_term_make_bindings<'a>(
    ft: &'a FlatTerm,
    pattern: &[ENodeOrVar],
    location: usize,
    bindings: &mut HashMap<Var, &'a FlatTerm>,
) {
    match &pattern[location] {
        ENodeOrVar::Var(var) => {
            if let Some(existing) = bindings.get(var) {
                if existing != &ft {
                    panic!(
                        "Invalid proof: binding for variable {:?} does not match between {:?} \n and \n {:?}",
                        var, existing, ft);
                }
            } else {
                bindings.insert(*var, ft);
            }
        }
        ENodeOrVar::ENode(node) => {
            // The node must match the rewrite or the proof is invalid.
            assert!(node.matches(&ft.node));
            let mut counter = 0;
            node.for_each(|child| {
                flat_term_make_bindings(&ft.children[counter], pattern, usize::from(child), bindings);
                counter += 1;
            });
        }
    }
}


// fn flat_term_rewrite<'a>(t: &'a FlatTerm, lhs: &PatternAst, rhs: &PatternAst) -> HashMap<Var, &'a FlatTerm> {
fn flat_term_binding<'a>(t: &'a FlatTerm, lhs: &PatternAst, rhs: &PatternAst) -> HashMap<Var, &'a FlatTerm> {
    let lhs_nodes = lhs.as_ref();
    // let rhs_nodes = rhs.as_ref();
    let mut bindings = Default::default();
    flat_term_make_bindings(t, lhs_nodes, lhs_nodes.len() - 1, &mut bindings);
    // FlatTerm::from_pattern(rhs_nodes, rhs_nodes.len() - 1, &bindings)
    return bindings.clone();
}

fn extract_rule_from_flat_term(t: &FlatTerm) -> Option<(Vec<String>, Sexp)> {
    match (t.forward_rule, t.backward_rule){
        (Some(rule), _) => {
            let node = t.node.clone();
            Some((vec!["fwd".to_string(), rule.as_str().to_string(), t.get_sexp().to_string()], t.get_sexp()))
        },
        (_, Some(rule)) => Some((vec!["bwd".to_string(), rule.as_str().to_string(), t.get_sexp().to_string()], t.get_sexp())),
        (None, None) => {
            for c in &t.children {
                match extract_rule_from_flat_term(&c) {
                    Some(mut rule) => {
                        return Some(rule)
                    },
                    None => ()
                }
            }
            return None
        }
    }
}


// if the rewrite is just patterns, then it can check it
fn check_rewrite<'a>(
    current: &'a FlatTerm,
    next: &'a FlatTerm,
    rewrite: &Rewrite,
    is_forward: bool) -> LeanRewriteInfo {
    if let Some(lhs) = rewrite.searcher.get_pattern_ast() {
        if let Some(rhs) = rewrite.applier.get_pattern_ast() {
            let rewritten = current.rewrite(lhs, rhs);
            if &rewritten != next {
                panic!("rewrite {:?} failed when rewriting {:?} to {:?}", rewrite, current, next);
            }
            let binding = flat_term_binding(current, lhs, rhs);
            let mut info = LeanRewriteInfo {
                rewrite: rewrite.name.to_string(),
                args: HashMap::new(),
                direction: if is_forward { String::from("fwd") } else { String::from("bwd") }
            };
            for (var, ft) in &binding {
                info.args.insert(var.to_string(), flat_term_to_raw_sexp(&ft).to_string());
            }
            return info;
        }
    }
    panic!("should have returned before when rewriting {:?} to {:?} with {:?}", current, next, rewrite);
}




fn check_rewrite_at
    (current: &FlatTerm,
    next: &FlatTerm,
    table: &HashMap<Symbol, &Rewrite>,
    is_forward: bool,
    out: &mut Vec<LeanRewriteInfo>) {
    if is_forward && next.forward_rule.is_some() {
        let rule_name = next.forward_rule.as_ref().unwrap();
        if let Some(rule) = table.get(rule_name) {
            out.push(check_rewrite(current, next, rule, is_forward));
        } else {
            // give up when the rule is not provided
        }
    } else if !is_forward && next.backward_rule.is_some() {
        let rule_name = next.backward_rule.as_ref().unwrap();
        if let Some(rule) = table.get(rule_name) {
            out.push(check_rewrite(next, current, rule, is_forward));
        } else {
            // give up when the rule is not provided

        }
    } else {
        for (left, right) in current.children.iter().zip(next.children.iter()) {
            check_rewrite_at(left, right, table, is_forward, out);
        }
    }
}


fn make_rule_table<'a>(
    rules: &'a Vec<Rewrite>
) -> HashMap<egg::Symbol, &'a Rewrite> {
    let mut table: HashMap<Symbol, &'a Rewrite> = Default::default();
    for r in rules {
        table.insert(r.name, &r);
    }
    table
}

pub fn check_proof(rules: Vec<Rewrite>, flat_explanation: &FlatExplanation) -> Vec<LeanRewriteInfo> {
    let rule_table = make_rule_table(&rules);
    assert!(!flat_explanation[0].has_rewrite_forward());
    assert!(!flat_explanation[0].has_rewrite_backward());

    let mut explanations : Vec<LeanRewriteInfo> = Vec::new();
    for i in 0..flat_explanation.len() - 1 {
        let current = &flat_explanation[i];
        let next = &flat_explanation[i + 1];

        let has_forward = next.has_rewrite_forward();
        let has_backward = next.has_rewrite_backward();
        assert!(has_forward ^ has_backward);

        if has_forward {
            check_rewrite_at(current, next, &rule_table, true, &mut explanations);
        } else {
            check_rewrite_at(current, next, &rule_table, false, &mut explanations);
        }
    }
    return explanations;
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
            .with_node_limit(4096)
            .with_egraph(graph)
            .with_explanations_enabled()
            .run(&new_rewrites);

            // println!("debug(graph):\n{:?} \n \n", runner.egraph.dump());

            if runner.egraph.find(lhs_id) ==  runner.egraph.find(rhs_id) {
                let mut explanation : Explanation<SymbolLang> = runner.explain_equivalence(&target_lhs_expr,
                    & target_rhs_expr);
                let flat_explanation : &FlatExplanation =
                    explanation.make_flat_explanation();

                // println!("DEBUG: explanation:\n{}\n", runner.explain_equivalence(&target_lhs_expr, &target_rhs_expr).get_flat_string());

                // let mut rules : Vec<Vec<String>> = Vec::new();
                let explanation = check_proof(new_rewrites, flat_explanation);
                // println!("DEBUG:iterating on the flat explanation \n{:?}\n..", flat_explanation);
                // for e in flat_explanation {
                //     let rule = extract_rule_from_flat_term(e);
                //     // eprintln!("expr: {} | forward_rule: {:?}", e.get_sexp(), rule);
                //     match rule  {
                //         Some((r, _sexp)) => {
                //             rules.push(r);
                //         }
                //         None => ()
                //     }
                // }
                Response::PerformRewrite { success: true, explanation: explanation }
            } else {
                Response::Error {error: format!("no rewrite found! egraph: {:?}", runner.egraph.dump()) }

            }
        }
    }
}


fn main_json() -> io::Result<()> {
    env_logger::init();
    // println!("1");
    let stdin = io::stdin();
    let mut stdout = io::stdout();
    // println!("2");
    let deserializer = serde_json::Deserializer::from_reader(stdin.lock());
    // println!("3");


    for read in deserializer.into_iter() {
        let response = match read {
            Err(err) => Response::Error {
                error: format!("Deserialization error: {}", err),
            },
            Ok(req) => {
                // println!("4");
                handle_request(req)
            }
        };
        // println!("5");
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
        .with_node_limit(4000)
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
