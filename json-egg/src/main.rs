// Code stolen from:
// https://github.com/mwillsey/egg-herbie-new/blob/8615590ff4ca07703c4b602f7d1b542e6465cfa6/src/main.rs
use egg::{rewrite as rw, *};
//use std::arch::x86_64::m128Ext;
use std::borrow::Borrow;
use std::rc::Rc;
use core::time::Duration;
use std::collections::HashMap;
// use std::f32::consts::E;
use std::{io};
use symbolic_expressions::Sexp;
// use std::{sync::mpsc::Receiver};
use std::str::FromStr;
use serde::{Deserialize, Serialize};
use egg::SymbolLang;
use egg::Explanation;
mod scheduler;

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
        timeout : u64,
        dump_graph : bool
    }
}

#[derive(Serialize,Debug)]
#[serde(rename_all = "kebab-case")]
pub struct LeanRewriteInfo {
    source: String, // the input expression before the rewrite
    rewrite: String, // name of the rewrite
    position : u32,
    mvars: HashMap<String, String>, // metavariable values.
    direction: String, // direction of the rewrite
    result: String // the output/result expression after the rewrite
}


#[derive(Serialize,Debug)]
#[serde(rename_all = "kebab-case")]
#[serde(tag = "response")]
enum Response {
    PerformRewrite {
        success: bool,
        // TODO: how does one use Sexp?
        explanation: Vec<LeanRewriteInfo>,
        stop_reason : String
    },
    Error { error: String }
}

#[derive(Serialize,Debug,PartialEq, Clone, Copy)]
enum Direction {
    Forward, Backward
}

// The invariant of a FlatTerm ensures there is at most one term
// with a forward/backward rule. Thus, the case where it is_some
// means this is the matching subterm.
fn get_rewrite_pattern_direction(t : &FlatTerm) -> Option<(Symbol,Direction)> {
    if let Some(rule) = t.forward_rule{
        return Some((rule, Direction::Forward ));
    } else if let Some(rule) = t.backward_rule{
        return Some((rule, Direction::Backward ));
    } else {
        for child in t.children.iter(){
            if let Some(res) = get_rewrite_pattern_direction(child){
                return Some(res);
            }
        }
    }
    return None;
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
    let expr = if t.node.is_leaf() {
        op
    } else {
        let mut vec = vec![op];
        for child in &t.children {
            vec.push(flat_term_to_raw_sexp(child));
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
    // TODO: eliminate if it is exactly the same as `FlatTerm.make_bindings`
    flat_term_make_bindings(t, lhs_nodes, lhs_nodes.len() - 1, &mut bindings);
    // FlatTerm::from_pattern(rhs_nodes, rhs_nodes.len() - 1, &bindings)
    return bindings.clone();
}

// if the rewrite is just patterns, then it can check it
fn build_rewrite_info<'a>(
    current: &'a FlatTerm,
    next: &'a FlatTerm,
    idx : u32,
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
                mvars: HashMap::new(),
                position : idx,
                direction: if is_forward { String::from("fwd") } else { String::from("bwd") },
                source: flat_term_to_raw_sexp(current).to_string(),
                result: flat_term_to_raw_sexp(next).to_string()
            };
            for (var, ft) in &binding {
                info.mvars.insert(var.to_string(), flat_term_to_raw_sexp(&ft).to_string());
            }
            return info;
        }
    }
    panic!("should have returned before when rewriting {:?} to {:?} with {:?}", current, next, rewrite);
}


fn check_lhs(
    lhs_node: &SymbolLang,
    lhs_rw: &[ENodeOrVar]
) -> bool {
    match &lhs_rw[lhs_rw.len() - 1] {
        ENodeOrVar::Var(var) => {
            panic!("unimplemented case: Var")
        }
        ENodeOrVar::ENode(node) => {
            // The node must match the rewrite or the proof is invalid.

            println!("checking {}({}).matches({})({})? {}", node, node.len(), lhs_node, lhs_node.len(), node.matches(lhs_node));
            return node.matches(lhs_node);
        }
    }
}

pub fn check_rewrite<'a>(
    current: &'a FlatTerm,
    next: &'a FlatTerm,
    rewrite: &Rewrite,
) -> bool {
    if let Some(lhs) = rewrite.searcher.get_pattern_ast() {
        if let Some(rhs) = rewrite.applier.get_pattern_ast() {
            let rewritten = current.rewrite(lhs, rhs);
            if &rewritten != next {
                return false;
            }
        }
    }
    true
}
/*
 Check if at the right point on the AST, if not,
 recursively call this function on children.
 Note that this is necessary because FlatTerm represents
 the full AST annotated with the rewrite information at the
 point of the subtree that is rewritten.
*/
fn get_rw_lhs
    (current: &FlatTerm,
    next: &FlatTerm,
    ) -> Option<Sexp> {
    if next.forward_rule.is_some() {
        return Some(flat_term_to_raw_sexp(&current));
    } else if next.backward_rule.is_some() {
        return Some(flat_term_to_raw_sexp(&next));
    } else{
        for (left, right) in current.children.iter().zip(next.children.iter()) {
            let res = get_rw_lhs(left, right);
            if res.is_some(){
                return res;
            }
        }
        return None;
    }
}

fn build_rewrite_info_at
    (current: &FlatTerm,
    next: &FlatTerm,
    rw : &Rewrite,
    rw_lhs : &Sexp,
    idx : u32,
    direction: Direction,
    out: &mut Vec<LeanRewriteInfo>) -> u32 {
    let mut cur_idx = idx;
    // this is the term
        if next.forward_rule.is_some() {
            //println!("at rewrite site: {}, incrementing to {}", current.node, cur_idx + 1);
            out.push(build_rewrite_info(current, next, cur_idx + 1, rw, direction == Direction::Forward));
            return cur_idx + 1;
        } else if next.backward_rule.is_some() {
            //println!("at rewrite site: {}, incrementing to {}", current.node, cur_idx + 1);
            out.push(build_rewrite_info(next, current, cur_idx + 1, rw, direction == Direction::Forward));
            return cur_idx + 1;
        } else{
            if let Some(lhs) = rw.searcher.get_pattern_ast(){
                if direction == Direction::Forward{
                    // check backward to see if the LHS was a match
                    if flat_term_to_raw_sexp(current) == *rw_lhs{
                        cur_idx = cur_idx + 1;
                        //println!("matched {} & incremented to {}",current.node, cur_idx);
                    }
                    else{
                        //println!("skipped {}, idx stays at: {}",current.node, cur_idx);
                    }
                } else{
                    // check backward to see if the LHS was a match
                    if flat_term_to_raw_sexp(next) == *rw_lhs{
                        cur_idx = cur_idx + 1;
                        //println!("matched {} & incremented to {}",current.node, cur_idx);
                    }
                    else{
                        //println!("skipped {}, idx stays at: {}",current.node, cur_idx);
                    }
                }
            }
            else{
                panic!("cannot get patten from rewrite");
            }
            for (left, right) in current.children.iter().zip(next.children.iter()) {
                cur_idx = build_rewrite_info_at(left, right, rw, rw_lhs, cur_idx, direction, out);
            }
            return cur_idx;
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

pub fn build_proof(rules: Vec<Rewrite>, flat_explanation: &FlatExplanation) -> Vec<LeanRewriteInfo> {
    let rule_table = make_rule_table(&rules);
    assert!(!flat_explanation[0].has_rewrite_forward());
    assert!(!flat_explanation[0].has_rewrite_backward());

    let mut explanations : Vec<LeanRewriteInfo> = Vec::new();
    for i in 0..flat_explanation.len() - 1 {
        let current = &flat_explanation[i];
        let next = &flat_explanation[i + 1];

        if let Some((rule_name, direction)) =  get_rewrite_pattern_direction(next){

          if let Some(rule) = rule_table.get(&rule_name) {
            if let Some(rw_lhs) = get_rw_lhs(current,next){
                build_rewrite_info_at(current, next,  rule, &rw_lhs, 0, direction, &mut explanations);
            }
        }
    }
    }
    return explanations;
}

fn handle_request(req: Request) -> Response {
    match req {
        Request::PerformRewrite { rewrites, target_lhs, target_rhs , timeout, dump_graph} => {

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
            //.with_scheduler(scheduler::BoundedGraphScheduler::default())
            //.with_scheduler(BackoffScheduler::default().with_initial_match_limit(8))
            //.with_scheduler(SimpleScheduler)
            .with_node_limit(999999)
            .with_time_limit(Duration::from_secs(timeout))
            .with_iter_limit(999999)
            .with_egraph(graph)
            .with_explanations_enabled()
            .with_hook(move |runner| {
                if runner.egraph.find(lhs_id) == runner.egraph.find(rhs_id) {
                    // panic!("same equivalence class".to_string());
                    Result::Err("now in same equivalence class".to_string())
                } else {
                    Result::Ok(())
                }

            })
            .run(&new_rewrites);

            if dump_graph{
                  runner.egraph.dot().to_dot("egraph_dump.dot").unwrap();
            }
            // println!("debug(graph):\n{:?} \n \n", runner.egraph.dump());

            if runner.egraph.find(lhs_id) ==  runner.egraph.find(rhs_id) {
                let mut explanation : Explanation<SymbolLang> = runner.explain_equivalence(&target_lhs_expr,
                    & target_rhs_expr);
                let flat_explanation : &FlatExplanation =
                    explanation.make_flat_explanation();

                // println!("DEBUG: explanation:\n{}\n", runner.explain_equivalence(&target_lhs_expr, &target_rhs_expr).get_flat_string());

                // let mut rules : Vec<Vec<String>> = Vec::new();
                let explanation = build_proof(new_rewrites, flat_explanation);
                Response::PerformRewrite { success: true, explanation: explanation, stop_reason : "proof found".to_string() }
            } else {
                let extractor = Extractor::new(&runner.egraph, AstSize);
                let (_, bestlhs) = extractor.find_best(lhs_id);
                let (_, bestrhs) = extractor.find_best(rhs_id);
                let mut explanationlhs : Explanation<SymbolLang> = runner.explain_equivalence(&target_lhs_expr,
                    & bestlhs);
                let mut explanationrhs : Explanation<SymbolLang> = runner.explain_equivalence(&target_rhs_expr,
                    & bestrhs);

                let flat_explanation_lhs : &FlatExplanation = explanationlhs.make_flat_explanation();
                let flat_explanation_rhs : &FlatExplanation = explanationrhs.make_flat_explanation();

                // println!("DEBUG: explanation:\n{}\n", runner.explain_equivalence(&target_lhs_expr, &target_rhs_expr).get_flat_string());

                // let mut rules : Vec<Vec<String>> = Vec::new();
                let mut explanation= build_proof(new_rewrites.clone(), flat_explanation_lhs);
                explanation.append(&mut build_proof(new_rewrites, flat_explanation_rhs));
                Response::PerformRewrite { success: false, explanation: explanation, stop_reason : format!("{:?}",runner.stop_reason)}
                //Response::Error {error: format!("no rewrite found! reason: {:?}", runner.stop_reason) }

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

impl<SymbolLang: FromOp> FromStr for RecExpr {
    type Err = RecExprParseError<SymbolLang::Error>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use RecExprParseError::*;

        fn parse_sexp_into<L: FromOp>(
            sexp: &Sexp,
            expr: &mut RecExpr,
        ) -> Result<Id, RecExprParseError<SymbolLang::Error>> {
            match sexp {
                Sexp::Empty => Err(EmptySexp),
                Sexp::String(s) => {
                    let node = L::from_op(s, vec![]).map_err(BadOp)?;
                    Ok(expr.add(node))
                }
                Sexp::List(list) if list.is_empty() => Err(EmptySexp),
                Sexp::List(list) => match &list[0] {
                    Sexp::Empty => unreachable!("Cannot be in head position"),
                    list @ Sexp::List(..) => Err(HeadList(list.to_owned())),
                    Sexp::String(op) => {
                        let arg_ids: Vec<Id> = list[1..]
                            .iter()
                            .map(|s| parse_sexp_into(s, expr))
                            .collect::<Result<_, _>>()?;
                        let node = L::from_op(op, arg_ids).map_err(BadOp)?;
                        Ok(expr.add(node))
                    }
                },
            }
        }

        let mut expr = RecExpr::default();
        let sexp = symbolic_expressions::parser::parse_str(s.trim()).map_err(BadSexp)?;
        parse_sexp_into(&sexp, &mut expr)?;
        Ok(expr)
    }
}

fn main() {
    // mainJson();
    main_json().unwrap();
    // main_group_check();

}
