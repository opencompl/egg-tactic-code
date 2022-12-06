/-
This file implements the key Equality Saturation data structure in Lean.
Authors: Siddharth Bhat
-/
-- import EggTactic.Sexp
import Lean.Data.HashMap
import Lean.Data.HashSet
open Lean Data
#check HashMap
#check StateRefT _ _ _
#check StateRefT' _ _ _

/-
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
            .with_node_limit(10000)
            .with_time_limit(Duration::from_secs(timeout))
            .with_iter_limit(10000)
            .with_egraph(graph)
            .with_explanations_enabled()
            .with_hook(move |runner| {
                if runner.egraph.find(lhs_id) == runner.egraph.find(rhs_id) {
                    // panic!("same equivalence class".to_string());
                    Result::Err("now in same equivalence class".to_string())
                } else {
                    Result::Ok(())
                }

            });


            eprintln!("DEBUG: saturating...");
            runner = runner.run(&new_rewrites);
            eprintln!("DEBUG:saturated!");

            if dump_graph{
                  runner.egraph.dot().to_dot("egraph_dump.dot").unwrap();
            }
            //
            let mut egraph = runner.egraph;
            egraph = egraph.without_explanation_length_optimization();
            // println!("debug(graph):\n{:?} \n \n", runner.egraph.dump());

            if egraph.find(lhs_id) ==  egraph.find(rhs_id) {
                 eprintln!("DEBUG: found equivalence");
                 eprintln!("DEBUG: explaining equivalence...");
                let mut explanation : Explanation<SymbolLang> = egraph.explain_equivalence(&target_lhs_expr,
                    & target_rhs_expr);
                 eprintln!("DEBUG: making flat explanation....");
                let flat_explanation : &FlatExplanation =
                    explanation.make_flat_explanation();

                // println!("DEBUG: explanation:\n{}\n", runner.explain_equivalence(&target_lhs_expr, &target_rhs_expr).get_flat_string());

                // let mut rules : Vec<Vec<String>> = Vec::new();
                 eprintln!("DEBUG: building proof...");
                let explanation = build_proof(new_rewrites, flat_explanation);
                 eprintln!("returning proof");
                Response::PerformRewrite { success: true, explanation: explanation, stop_reason : "proof found".to_string() }
            } else {
                let extractor = Extractor::new(&egraph, AstSize);
                let (_, bestlhs) = extractor.find_best(lhs_id);
                let (_, bestrhs) = extractor.find_best(rhs_id);
                let mut explanationlhs : Explanation<SymbolLang> = egraph.explain_equivalence(&target_lhs_expr,
                    & bestlhs);
                let mut explanationrhs : Explanation<SymbolLang> = egraph.explain_equivalence(&target_rhs_expr,
                    & bestrhs);

                let flat_explanation_lhs : &FlatExplanation = explanationlhs.make_flat_explanation();
                let flat_explanation_rhs : &FlatExplanation = explanationrhs.make_flat_explanation();
runner.
                // println!("DEBUG: explanation:\n{}\n", egraph.explain_equivalence(&target_lhs_expr, &target_rhs_expr).get_flat_string());

                // let mut rules : Vec<Vec<String>> = Vec::new();
                let mut explanation= build_proof(new_rewrites.clone(), flat_explanation_lhs);
                explanation.append(&mut build_proof(new_rewrites, flat_explanation_rhs));
                Response::PerformRewrite { success: false, explanation: explanation, stop_reason : format!("{:?}",runner.stop_reason)}
                //Response::Error {error: format!("no rewrite found! reason: {:?}", runner.stop_reason) }


-/
structure Symbol where
  string: String
  deriving BEq, Hashable, Inhabited



structure Eid where
  val : UInt64
  deriving BEq, Hashable, Inhabited

def Eid.toNat (e: Eid) : Nat := e.val.toNat

structure SymbolLang where 
  op: Symbol
  children: Array Eid
  deriving BEq, Inhabited, Hashable

def SymbolLang.leaf (s: Symbol): SymbolLang := { op := s, children := #[] }

-- shallow match
def symbolLang.matches (s t: SymbolLang): Bool := 
  s.op == t.op && (s.children.size == t.children.size)



-- https://github.com/egraphs-good/egg/blob/main/src/eclass.rs#L10
structure Eclass where
  id : Eid
  nodes: Array SymbolLang
  parents: Array (SymbolLang × Eid)

-- https://github.com/egraphs-good/egg/blob/main/src/explain.rs#L20
inductive Justification where
| Rule: Symbol -> Justification -- A symbol is an interned string
| Congruence: Justification
  deriving BEq, Inhabited

def Justification.isCongruence (j: Justification) : Bool :=
  match j with
  | Justification.Congruence => true
  | _ => false

-- https://github.com/egraphs-good/egg/blob/main/src/explain.rs#L29
structure Connection where
    next: Eid -- Id of the parent
    current: Eid
    justification: Justification
    is_rewrite_forward: Bool
  deriving BEq, Inhabited

-- https://github.com/egraphs-good/egg/blob/main/src/explain.rs#L38
structure ExplainNode where
  node: SymbolLang
  neighbours: Array Connection -- neighbors includes parent connections
  parent_connection: Connection
  --it was inserted because:
  -- 1) it's parent is inserted (points to parent enode)
  -- 2) a rewrite instantiated it (points to adjacent enode)
  -- 3) it was inserted directly (points to itself)
  -- if 1 is true but it's also adjacent (2) then either works and it picks 2
  existence_node: Eid
  deriving BEq, Inhabited


structure Explain where
    uncanon_memo : HashMap SymbolLang Eid
    explainfind: Array ExplainNode
deriving Inhabited

def Explain.add (explain: Explain) (node: SymbolLang) (set: Eid) (existence_node: Eid): Eid × Explain :=
  let uncanon_memo := explain.uncanon_memo.insert node set
  let explainfind := explain.explainfind.push
    { node := node
    , neighbours := Array.empty
    , parent_connection :=
      { next := set
      , current := set
      , justification := Justification.Congruence
      , is_rewrite_forward := false
      }
    , existence_node := existence_node }
  (set, { explain with uncanon_memo, explainfind })

-- I need lenses.
def Explain.set_existence_reason (explain: Explain) (node existence_node: Eid): Explain :=
  let nodeExplain := explain.explainfind.get! node.toNat
  let nodeExplain := { nodeExplain with existence_node }
  let explainfind := explain.explainfind.set! node.toNat nodeExplain
  { explain with explainfind }

def Explain.union (explain: Explain) (node1 node2: Eid) (justification: Justification)
  (new_rhs: Bool) : Explain :=
  /-
  let explain :=
    if new_rhs then {
        explain.set_existence_reason node2 node1
    } else {
        explain
    }
  let explain := explain.make_leader node1
  -/
  sorry


structure UnionFind where
  parents: Array Eid
deriving BEq, Inhabited

def UnionFind.make_set (uf: UnionFind): Eid × UnionFind :=
  let newId := UInt64.ofNat uf.parents.size
  (Eid.mk newId, {parents := uf.parents.push (Eid.mk newId)})

def UnionFind.size (uf: UnionFind): Nat :=
  uf.parents.size

def UnionFind.parent_ (uf: UnionFind) (e : Eid): Eid :=
  uf.parents.get! (UInt64.toNat e.val)

/- How do do this purely functionally? Good question. Can store witness that {a[i] <= i}. -/
/- TODO: path compression -/
partial def UnionFind.find (uf: UnionFind) (e : Eid): Eid :=
  let rec loop (e : Eid): Eid :=
    let p := uf.parent_ e
    if p == e then e else loop p
  loop e

partial def UnionFind.union (uf: UnionFind) (e1 e2 : Eid): UnionFind :=
  let p1 := uf.find e1
  let p2 := uf.find e2
  if p1 == p2 then uf else
    let newParents := uf.parents.set! (UInt64.toNat p1.val) p2
    {parents := newParents}

-- https://github.com/egraphs-good/egg/blob/main/src/egraph.rs#L54
structure Egraph where
  unionfind: UnionFind
  explain: Explain
  classes: HashMap Eid Eclass
deriving Inhabited

abbrev EgraphM (α : Type):= EStateM Empty Egraph α


-- https://github.com/egraphs-good/egg/blob/main/src/subst.rs#L15
structure Var where
  name: Symbol
  deriving BEq, Hashable, Inhabited

-- https://github.com/egraphs-good/egg/blob/main/src/subst.rs#L52
abbrev Subst := HashMap Var SymbolLang

-- https://github.com/egraphs-good/egg/blob/main/src/pattern.rs#L73
inductive PatternAst
| atom: String → PatternAst
| list: List PatternAst → PatternAst
| var: Var → PatternAst
deriving BEq, Inhabited

def PatternAst.compact: PatternAst → PatternAst := sorry

-- https://github.com/egraphs-good/egg/blob/main/src/pattern.rs#L251
structure SearchMatches where
  eclass: Eid
  substs: Array Subst
  ast: PatternAst
  deriving Inhabited

-- https://github.com/egraphs-good/egg/blob/e8cc799a32a94b3b5ad5cb5871bc957245584232/src/rewrite.rs#L162
-- class Searcher (α: Type) where
--   search_eclass_with_limit (egraph: Egraph) (eclass: Eid) (limit: USize) (searcher: α): Option SearchMatches

-- structure Applier (α: Type) where
--   apply_one (eclass: Eid) (subst: Subst) (searcher_ast: Option PatternAst) (rule_name: Symbol): EgraphM (Array Eid)


structure Reg where
  reg: USize
  deriving BEq, Hashable

inductive SymbolLangOrReg
| sexp: SymbolLang → SymbolLangOrReg
| reg: Reg → SymbolLangOrReg

-- https://github.com/egraphs-good/egg/blob/e8cc799a32a94b3b5ad5cb5871bc957245584232/src/machine.rs#L23
inductive Instruction
| Bind (node: SymbolLang) (i out: Reg) : Instruction
| Compare (i j: Reg): Instruction
| Lookup (term: Array (SymbolLangOrReg)) (i: Reg) : Instruction
| Scan (out: Reg) : Instruction

structure Compiler where
    v2r: HashMap Var Reg
    free_vars: Array (HashSet Var)
    subtree_size: Array USize
    todo_nodes: HashMap (Eid×Reg) SymbolLang
    instructions: Array Instruction
    next_reg: Reg

-- https://github.com/egraphs-good/egg/blob/e8cc799a32a94b3b5ad5cb5871bc957245584232/src/machine.rs#L17
structure Program where
  instructions: Array Instruction
  subst: Subst

def Program.compile_from_pat (pat: PatternAst): Program := sorry

structure Pattern  where
  ast: PatternAst
  program: Program

def Pattern.new (ast: PatternAst): Pattern :=
  let ast := ast.compact
  let program := Program.compile_from_pat ast
  {ast, program}


-- A pattern is both a Searcher and an Applier.

structure Rewrite where
  name: Symbol
  searcher: Pattern
  applier: Pattern

def Rewrite.new (name: Symbol) (lhs: PatternAst) (rhs: PatternAst): Rewrite :=
  let searcher := Pattern.new lhs
  let applier := Pattern.new rhs
  {name, searcher, applier}

def Rewrite.search (rw: Rewrite) (egraph: Egraph): Array SearchMatches
  := sorry
def Rewrite.apply (rw: Rewrite) (ms: Array SearchMatches) (rule_name: Symbol): EgraphM (Array Eid)
  := sorry

def Egraph.lookup_internal (egraph: Egraph) (expr: SymbolLang) : EgraphM (Option Eid) := do
  pure none
def Egraph.find (egraph: Egraph) (id : Eid) : Eid := egraph.unionfind.find id



def Egraph.make_new_eclass (egraph: Egraph) (expr: SymbolLang) : EgraphM Eid := do
  let (id, unionfind) := egraph.unionfind.make_set
  let eclass := Eclass.mk id #[expr] #[]
  let classes := egraph.classes.insert id eclass
  let egraph := { egraph with unionfind, classes }
  set egraph
  pure id

def Egraph.add_internal (egraph: Egraph) (e: SymbolLang) : EgraphM Eid := do
  match ← egraph.lookup_internal e with -- TODO: use if let?
  | .some existing_id => do
    let existing_id := egraph.find existing_id
    match egraph.explain.uncanon_memo.find? e with
    | .some existing_expl => do
        return existing_expl
    | .none =>
        let (new_id, unionfind) := egraph.unionfind.make_set
        let (_, explain) := egraph.explain.add e new_id new_id
        let explain := explain.union existing_id new_id (Justification.Congruence) (new_rhs := true)
        set { egraph with unionfind, explain }
        return new_id
  | .none =>
    let id ← egraph.make_new_eclass e
    let (_, explain) := egraph.explain.add e id id
    set { egraph with explain }
    return id


def EgraphM.add_expr (expr: SymbolLang) : EgraphM Eid  := do
  let egraph ← get
  let id ← egraph.add_internal expr
  return egraph.find id



def Egraph.rebuild : EgraphM Unit := sorry


inductive StopReason where
| Saturated: StopReason
| IterationLimit: USize → StopReason
| NodeLimit: USize → StopReason
| TimeLimit: Float → StopReason
| Other: String → StopReason
deriving BEq, Inhabited

structure Iteration where
  stop_reason: Option StopReason
deriving BEq, Inhabited

structure Runner where
  egraph: Egraph


def Runner.run_one (runner: Runner) (rules: Array Rewrite): EgraphM Iteration := do
  let egraph ← get
  let mut mss : Array (Array SearchMatches) := #[]
  for rule in rules do {
    mss := mss.push (rule.search egraph)
    -- check_limits
  }
  for (ms, rule) in mss.zip rules do {
      let ids ← rule.apply ms rule.name
  }
  return {stop_reason := none}

partial def Runner.run (runner: Runner) (rules: Array Rewrite): EgraphM Unit := do
  let iter ← runner.run_one rules
  if iter.stop_reason.isSome then
    pure ()
  else
    runner.run rules


-- Run the runner till the e-classes of a, b are equal.
partial def Runner.runTillEq (runner: Runner) (rules: Array Rewrite) (a b: Eid): EgraphM Unit := do
  let iter ← runner.run_one rules
  if iter.stop_reason.isSome then
    pure ()
  else
    runner.run rules

-- mutual
-- TODO: implement 'abbrev' in mutual block.

inductive TreeTerm where
| mk
  (node: SymbolLang)
  (backward_rule: Option Symbol)
  (forward_rule: Option Symbol)
  (child_proofs: Array (Array TreeTerm))
  -- (children: Array TreeExplanation): TreeTerm
  deriving Inhabited

abbrev TreeExplanation :=  Array TreeTerm
-- end

def TreeTerm.new (node: SymbolLang) (child_proofs: Array TreeExplanation): TreeTerm := 
  TreeTerm.mk 
    (node := node)
    (backward_rule := .none)
    (forward_rule := .none)
    (child_proofs := child_proofs)


inductive FlatTerm where
| mk
  (node: SymbolLang)
  (backward_rule: Option Symbol)
  (forward_rule: Option Symbol)
  (children: Array FlatTerm): FlatTerm

/-
inductive SymbolLangLens
| atom: SymbolLangLens
| list: Int → SymbolLangLens → SymbolLangLens

inductive FlatTermLensed where
| mk
  (node: SymbolLang)
  (loc: SymbolLangLens)
  (rule: Symbol)
  (forward: Bool) -- TODO: use enum
  : FlatTermLensed
-/

-- https://github.com/egraphs-good/egg/blob/e8cc799a32a94b3b5ad5cb5871bc957245584232/src/explain.rs#LL85C47-L85C47
abbrev TreeExplanation := Array TreeTerm
-- https://github.com/egraphs-good/egg/blob/e8cc799a32a94b3b5ad5cb5871bc957245584232/src/explain.rs#L93
abbrev FlatExplanation := Array FlatTerm



abbrev ExplainCache := HashMap (Eid × Eid) TreeTerm
abbrev NodeExplanationCachce := HashMap Eid TreeTerm

-- TODO: convert to StateRefT
structure ExplainState where
  cache: ExplainCache
  node_explanation_cache: NodeExplanationCachce
deriving Inhabited



abbrev ExplainM α := EStateM Empty ExplainState α

partial def Explain.node_to_explanation (explain: Explain) (id: Eid) : ExplainM TreeTerm := do
  match (← get).node_explanation_cache.find? id with
  | .some explanation => pure explanation
  | .none => do
      let node : ExplainNode := explain.explainfind[id.toNat]!
      let symbolLang := node.node
      let mut sofar : Array (TreeTerm) := #[]
      let mut children : Array (Array TreeTerm) := #[]
      -- Disgustingly slow computation here! What the hell, this is n^2.
      for child in symbolLang.children do 
        sofar := sofar.push (← explain.node_to_explanation child)
        children := children.push sofar
      return TreeTerm.new symbolLang children

def Explain.ancestor (explain: Explain) (child: Eid): Eid := 
    explain.explainfind[child.toNat]!.parent_connection.next

partial def Explain.common_ancestor_run (explain: Explain) (left right: Eid) (seen_left seen_right: HashSet Eid): Eid := 
  let seen_left := seen_left.insert left
  let seen_right := seen_right.insert right
  if seen_right.contains left then left 
  else if seen_left.contains right then right
  else 
    explain.common_ancestor_run (explain.ancestor left) (explain.ancestor right) seen_left seen_right
partial def Explain.common_ancestor (explain: Explain) (left right: Eid): Eid := explain.common_ancestor_run left right {} {}

partial def Explain.get_connections (explain: Explain) (node ancestor: Eid): Array Connection := Id.run do
  let rec loop (node: Eid) (nodes: Array Connection) : Array Connection := 
    if node == ancestor then nodes
    else 
      let parent := explain.explainfind[node.toNat]!.parent_connection
      let next := parent.next
      let nodes := nodes.push parent
      if next == ancestor then nodes
      else 
        let node := next 
        loop node nodes
  loop node #[]


    
def Explain.get_path_unoptimized (explain: Explain) (left right: Eid): ExplainM (Array Connection × Array Connection) := do 
  let ancestor := explain.common_ancestor left right
  let left_connections : Array Connection := explain.get_connections left ancestor
  let right_connections : Array Connection := explain.get_connections left ancestor
  return (left_connections, right_connections)

def Explain.explain_adjacent (explain: Explain) (connection: Connection): ExplainM TreeTerm := do 
  let fingerprint : Eid × Eid := (connection.current, connection.next)
  -- if let .some answer := (← get).cache.find? fingerprint
  -- then return answer
  let term : TreeTerm := match connection.justification with
  | .Rule name => sorry 
  | .Congruence => sorry
  term
  

partial def Explain.explain_enodes (explain: Explain) (left right: Eid):  ExplainM TreeExplanation := do
  let mut proof ←  explain.node_to_explanation left
  let (left_connections, right_connections) ← explain.get_path_unoptimized left right
  let mut i := 0
  for connection in (left_connections.append right_connections.reverse) do
    let connection :=
      if i >= left_connections.size
      then { connection with
              is_rewrite_forward := !connection.is_rewrite_forward
             , next := connection.current
             , current := connection.next
            }
      else connection
    proof := proof.push (explan.explain_adjacent connection)
    i := i + 1
  pure proof

partial def Egraph.explain_equivalence (a b : Eid): EgraphM TreeExplanation := do
  let explain_state : ExplainState := {cache := {}, node_explanation_cache := {}}
  let explanation : TreeExplanation :=
    match (explain_enodes (← get) a b).run explain_state with
    | .ok v _exlain_state => v
    | .error e _explain_state => nomatch e
  return explanation

def TreeExplanation.toFlatExplanation : TreeExplanation -> FlatExplanation := sorry
