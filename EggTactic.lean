import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson

open Lean Meta Elab Tactic
open Lean.Elab.Term
open IO
open System

-- Path to the egg server.
def egg_server_path : String := 
  "json-egg/target/debug/egg-herbie"

structure EggRewrite where
  name: String
  lhs: String
  rhs: String

inductive EggRewriteDirection where
  | Forward
  | Backward
  deriving Inhabited, DecidableEq

open EggRewriteDirection

structure EggExplanation where
  direction: EggRewriteDirection -- direction of the rewrite
  rule: String -- name of the rewrite rule

instance : ToString EggExplanation where
  toString expl :=
    let dir := if expl.direction == Forward then "fwd" else "bwd"
    toString f!"[{dir}, {expl.rule}]"

-- | parse a fragment of an explanation into an EggRewrite
def parseExplanation (j: Json) : Except String EggExplanation := do
  let l <- j.getArr?
  let ty <- l[0].getStr?
  let d <- match ty with
  | "fwd" => pure Forward
  | "bwd" => pure Backward
  | other => throw (toString f!"unknown direction {other} in |{j}")
  let r <- l[1].getStr?
  return { direction := d, rule := r}

-- | Actually do the IO. This incurs an `unsafe`.
unsafe def unsafePerformIO [Inhabited a] (io: IO a): a :=
  match unsafeIO io with
  | Except.ok a    =>  a
  | Except.error e => panic! "expected io computation to never fail"

-- | Circumvent the `unsafe` by citing an `implementedBy` instance.
@[implementedBy unsafePerformIO]
def performIO [Inhabited a] (io: IO a): a := Inhabited.default


def surround_quotes (s: String): String :=
 "\"" ++ s ++ "\""
def surround_escaped_quotes (s: String): String :=
 "\\\"" ++ s ++ "\\\""


def EggRewrite.toJson (rewr: EggRewrite) :=
  "{"
    ++ surround_quotes "name" ++ ":" ++ surround_quotes rewr.name ++ ","
    ++ surround_quotes "lhs" ++ ":" ++ surround_quotes rewr.lhs ++ ","
    ++ surround_quotes "rhs" ++ ":" ++ surround_quotes rewr.rhs ++
  "}"

instance : ToString EggRewrite where
  toString rewr := rewr.toJson


structure EggRequest where
  target_lhs: String
  target_rhs: String
  rewrites: List EggRewrite

def EggRequest.toJson (e: EggRequest): String :=
  "{"
  ++ surround_quotes "request"  ++  ":" ++ surround_quotes "perform-rewrite" ++ ","
  ++ surround_quotes "target-lhs"  ++  ":" ++ surround_quotes (e.target_lhs) ++ ","
  ++ surround_quotes "target-rhs"  ++  ":" ++ surround_quotes (e.target_rhs) ++ ","
  ++ surround_quotes "rewrites" ++ ":" ++ "[" ++ String.intercalate "," (e.rewrites.map EggRewrite.toJson) ++ "]"
  ++ "}"

def Lean.Json.getStr! (j: Json): String :=
  match j with
  | Json.str a => a
  | _ => toString (f!"[ERROR: expected |{j}| to be a JSON string.]")

def Lean.Json.getArr! (j: Json): Array Json :=
  match j with
  | Json.arr a => a
  | _ => #[]

def Lean.List.contains [DecidableEq a] (as: List a) (needle: a): Bool := 
  as.any (. == needle)
 
def lean_list_get? (as: List a) (n: Nat): Option a := 
match n with 
| 0 => match as with | .nil => none | .cons a as => some a
| n + 1 => match as with | .nil => none |.cons a as => lean_list_get? as n

def Lean.List.get? (as: List a) (n: Nat): Option a := lean_list_get? as n 

partial def exprToString_ (e: Expr) (bound: List Name): MetaM String :=   
match e with 
  | Expr.const  name levels data => pure (name.toString)
  | Expr.bvar ix data => 
    match (bound.get? ix) with 
    | some name => pure ("?" ++ name.toString)
    | none => throwError s!"no bound name known for index {ix} | expr: {e} | bound: {bound}"
  | Expr.fvar id data => 
      if bound.contains id.name
      then throwError s!"found bound name: {id.name}"
      else pure (id.name.toString)
  | Expr.lit (.natVal n) data => pure (toString n)
  | Expr.app     l r data => do 
     let lstr <- exprToString_ l bound
     let rstr <- exprToString_ r bound
     pure $ "(ap " ++ lstr ++ " " ++ rstr ++ ")"
--   | Expr.lit lit data => lit.
--  | Expr.forallE name type body data => exprToString_ body (name::bound)
  | _ => throwError s!"unimplemented expr_to_string ({e.ctorName}): {e}"



def exprToString (e: Expr) (bound: List Name) : MetaM Format := do
  let s <- exprToString_ e bound
  -- pure (surround_escaped_quotes s)
  pure s
    -- if e.isFVar then toString (lctx.getFVar! e).userName else toString e

def findMatchingExprs (t : Expr) : TacticM (List Name) :=
  withMainContext do
    let lctx <- getLCtx
    lctx.foldlM (init := []) fun (accum : List Name) (ldecl: LocalDecl) => do
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_type <- inferType ldecl_expr
      let res := if ldecl_type == t then ldecl.userName :: accum else accum
      return res -- why won't return $ if ... work?

open Lean.Meta

#check withLCtx 

structure EggState where
  ix: Nat
  name2expr: List (Int × Expr)
  deriving Inhabited

instance : ToString EggState where
  toString expl :=
    toString f!"[ix:{expl.ix}]"

-- | find an expression with the given index as needle.
def EggState.findExpr (state: EggState) (needle: Int): Option Expr := 
    let rec go (l: List (Int × Expr)): Option Expr :=
      match l with 
      | [] => Option.none
      | ((ix, e)::xs) => if ix == needle then some e else go xs 
    go state.name2expr


partial def gensymRewriteName (rw: Expr) (state: EggState): (String × EggState) :=
  let i := state.ix
  (toString i, { ix := i + 1, name2expr := ((i, rw) :: state.name2expr) : EggState })

def expr_get_forall_bound_vars: Expr -> List Name 
| Expr.forallE name ty body data => name :: expr_get_forall_bound_vars body 
| _ => []

def Lean.Expr.getForallBoundVars: Expr -> List Name := expr_get_forall_bound_vars

-- | disgusting. Please fix to a real parser later @andres
partial def parseInt (n: Int) (s: String): Option Int :=
  if n < 0 
  then none
  else if toString n == s
  then some n
  else parseInt (n - 1) s


partial def addUniversalEqualitiesForall (rw: Expr) (rw_type: Expr) (state: EggState): TacticM ((List EggRewrite) × EggState) := 
  if rw_type.isForall
  then do 
    let rw_type_body : Expr := rw_type.getForallBody
    let rw_type_vars: List Name := rw_type.getForallBoundVars
    let eqbody? <- matchEq? rw_type_body
    let (rw_eq_type, rw_lhs, rw_rhs)  <-  
        match eqbody? with
        | some (rw_eq_type, rw_lhs, rw_rhs) => 
            pure (rw_eq_type, rw_lhs, rw_rhs) 
        | none => throwError f!"expected ∀ expression type to have equality body: {rw_type}"
    let lhs <- exprToString rw_lhs rw_type_vars
    let rhs <- exprToString rw_rhs rw_type_vars
    -- dbg_trace "LHS: {lhs} | RHS: {rhs}"
    let (rw_name, state) := gensymRewriteName rw state
    let egg_rewrite := { name := rw_name, lhs := toString lhs, rhs := toString rhs : EggRewrite }
    return ([egg_rewrite], state)
  else throwError "expected ∀"

partial def addEqualities (bound: List Name) (equalityTermType : Expr) (accum : List EggRewrite) (rw_stx : Syntax) (state: EggState): TacticM ((List EggRewrite) × EggState) :=
  withMainContext do
    let rw <-  (Lean.Elab.Tactic.elabTerm rw_stx (Option.none))
    let rw_type <- inferType rw
    let lctx <- getLCtx
    match (<- matchEq? rw_type) with
   | some (rw_eq_type, rw_lhs, rw_rhs) => do
      -- | check that rewrite is of the correct type.
      let is_well_typed <- isExprDefEq rw_eq_type equalityTermType
      if is_well_typed
      then
        let lhs_name <- exprToString rw_lhs bound
        let rhs_name <- exprToString rw_rhs bound
        let (rw_name, state) := gensymRewriteName rw  state
        -- dbg_trace "1) rw_name: {rw_name} | rw_stx: {rw_stx} | rw: {rw} | rw_eq_type: {rw_eq_type} | lhs: {lhs_name} | rhs: {rhs_name}"
        let egg_rewrite := { name := rw_name, lhs := toString lhs_name, rhs := toString rhs_name : EggRewrite }
        return (egg_rewrite :: accum, state)
      else throwError (f!"Rewrite |{rw_stx} (term={rw})| incorrectly equates terms of type |{rw_eq_type}|." ++
      f!" Expected to equate terms of type |{equalityTermType}|")
   | none => do
      match rw_type with
        | Expr.forallE n t b _ => do
          -- vvv new code, that implements the rules of the form (mul ?a ?b) = (mul ?b ?a)
          --  let (ys', state) <- (addEqualities (n::bound) equalityTermType [] (Syntax.mkApp rw_stx #[mkIdent n]) state)
          let (ys, state) <- addUniversalEqualitiesForall rw rw_type state
          /-
          let rw_type_body : Expr := rw_type.getForallBody
          let rw_type_vars: List Name := rw_type.getForallBoundVars
          dbg_trace "forall expr: {rw_type} | vars: {rw_type_vars} | body: {rw_type_body}"
          -/
          /-
          match (<- matchEq? rw_type_body) with
            | some (rw_eq_type, rw_lhs, rw_rhs) => 
                throwError "unimplemented" 
            | none => throwError f!"expected ∀ expression type to have equality body: {rw_type}"
          -- vvv old code, that is responsible for applying the values to all combinations vvv
          -/
          let possibleInsts : List Name <- findMatchingExprs t
          let applications : List Syntax <- possibleInsts.mapM λ i:Name =>
               let i_stx := Array.mk [mkIdent i]
               let res := Syntax.mkApp rw_stx i_stx
               return res
          let (applyInsts', state)  <-
              applications.foldlM 
                (fun xs_and_state stx => do
                  let xs := xs_and_state.fst 
                  let state := xs_and_state.snd 
                  let (xs', state) <- (addEqualities bound equalityTermType xs stx state)
                  return (xs', state)) (accum, state)
          return (applyInsts' ++ ys, state)
           
        | _ => throwError "Rewrite |{rw_stx} (term={rw})| must be an equality. Found |{rw} : {rw_type}| which is not an equality"
     -- let tm <- Lean.Elab.Tactic.elabTermEnsuringType rw_stx (Option.some target)
     -- let tm <- Term.elabTerm rw_stx (Option.some target)
     -- return (tm :: accum)

elab "rawEgg" "[" rewrites:ident,* "]" : tactic =>  withMainContext  do
  let goals <- getGoals
  let target <- getMainTarget
  -- let (target_newMVars, target_binderInfos, target_eq_type) ← forallMetaTelescopeReducing target
  --  Use the helpers to match because it puts stuff in WHNF
  match (<- matchEq? target) with
  | none => do
    dbg_trace f!"target is not an equality: |{target}|"
    throwError "target {target} is not an equality"
  | some (equalityTermType, equalityLhs, equalityRhs) =>
    let maingoal <- getMainGoal
    -- | elaborate the given hypotheses as equalities.
    -- These are the rewrites we will perform rewrites with.
    -- For arrows, we instantiate them as we can with variables from the context.
    let initState := { ix := 0, name2expr := [] : EggState}
    let (egg_rewrites , state)  <- rewrites.getElems.foldlM (init := ([], initState)) 
        (fun xs_and_state stx => do 
          let xs := xs_and_state.fst 
          let state := xs_and_state.snd 
          let (xs', state) <- (addEqualities (bound := []) equalityTermType xs stx state)
          return (xs', state))
    let explanations : List EggExplanation <- (liftMetaMAtMain fun mvarId => do
      -- let (h, mvarId) <- intro1P mvarId
      -- let goals <- f mvarId (mkApp (mkConst ``Or.elim) (mkFVar h))
      let lctx <- getLCtx
      let mctx <- getMCtx
      let hypsOfEqualityTermType <- lctx.foldlM (init := []) (fun accum decl =>  do
          if decl.type == equalityTermType
          then return (decl.userName, decl.type) :: accum
          else return accum)

      let out := "\n====\n"
      let lhs_str : Format <- exprToString equalityLhs (bound := [])
      let rhs_str : Format <- exprToString equalityRhs (bound := [])
      let out := out ++ f!"-eq.t: {equalityTermType}"
      let out := out ++ f!"-eq.lhs: {equalityLhs} / {lhs_str}"
      let out := out ++ f!"-eq.rhs: {equalityRhs} / {rhs_str}\n"
      let out := out ++ f!"-hypothesis of type [eq.t]: {hypsOfEqualityTermType}\n"
      -- let out := out ++ f!"-hypotheses of [eq.t = eq.t]: {hypsOfEquality}\n"
      let out := out ++ f!"-hypotheses given of type [eq.t = eq.t]: {egg_rewrites}\n"
      -- let out := out ++ m!"-argumentStx: {argumentStx}\n"
      -- let out := out ++ m!"-mainGoal: {maingoal}\n"
      -- let out := out ++ m!"-goals: {goals}\n"
      -- let out := out ++ m!"-target: {target}\n"
      let out := out ++ "\n====\n"
      -- throwTacticEx `rawEgg mvarId out
      dbg_trace out
      -- | forge a request.
      let req : EggRequest := {
        target_lhs := toString (lhs_str)
        , target_rhs := toString (rhs_str)
        , rewrites := egg_rewrites}
      -- | Invoke accursed magic to send the request.
      let req_json : String := req.toJson
      -- | Steal code from |IO.Process.run|
      dbg_trace "2) sending request:---\n {egg_server_path}\n{req_json}\n---"
      let egg_server_process <- IO.Process.spawn
        { cmd := egg_server_path,
          -- stdin := IO.Process.Stdio.piped,
          stdout := IO.Process.Stdio.piped,
          stdin := IO.Process.Stdio.piped,
          -- stdout := IO.Process.Stdio.null,
          stderr := IO.Process.Stdio.null
        }
      FS.writeFile s!"/tmp/egg.json" req_json
      dbg_trace "3) Spanwed egg server process. Writing stdin..."
      let (stdin, egg_server_process) ← egg_server_process.takeStdin
      stdin.putStr req_json
      dbg_trace "5) Wrote stdin. Setting up stdout..."
      let stdout ← IO.asTask egg_server_process.stdout.readToEnd Task.Priority.dedicated
      dbg_trace "6) Setup stdout. Waiting for exitCode..."
      let exitCode : UInt32 <- egg_server_process.wait
      dbg_trace "7) got exitCode ({exitCode}). Waiting for stdout..."
      let stdout : String <- IO.ofExcept stdout.get
      -- dbg_trace "8) read stdout."
      -- let stdout : String := "STDOUT"
      dbg_trace ("9)stdout:\n" ++ stdout)
      let out_json : Json <- match Json.parse stdout with
        | Except.error e => throwTacticEx `rawEgg mvarId e
        | Except.ok j => pure j
      dbg_trace ("10)stdout as json:\n" ++ (toString out_json))
      let response_type := (out_json.getObjValD "response").getStr!
      dbg_trace ("11)stdout response: |" ++ response_type ++ "|")
      if response_type == "error"
      then
        throwTacticEx `rawEgg mvarId (toString out_json)
      else
        dbg_trace "12) Creating explanation..."
        let explanationE : Except String (List EggExplanation) := do
           -- extract explanation field from response
           let expl <- (out_json.getObjVal? "explanation")
           -- cast field to array
           let expl <- Json.getArr? expl
           -- map over each element into an explanation
           let expl <- expl.mapM parseExplanation
           return expl.toList
        let explanation <- match explanationE with
          | Except.error e => throwTacticEx `rawEgg mvarId (e)
          | Except.ok v => pure v
        dbg_trace ("13) explanation: |" ++ String.intercalate " ;;; " (explanation.map toString) ++ "|")
        return (explanation))

    for e in explanations do {
      let lctx <- getLCtx
      dbg_trace (f!"14) aplying rewrite {e}")
        let name : String := e.rule
        let ldecl_expr <- match (parseInt 100 name) >>= (state.findExpr) with
        | some ix => pure ix 
        | none => do 
           throwTacticEx `rawEgg (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
      let ldecl_expr <- if e.direction == Backward then mkEqSymm ldecl_expr else pure ldecl_expr
      let rewrite_result <- rewrite (<- getMainGoal) (<- getMainTarget) ldecl_expr
      dbg_trace (f!"rewritten to: {rewrite_result.eNew}")
      let mvarId' ← replaceTargetEq (← getMainGoal) rewrite_result.eNew rewrite_result.eqProof
      replaceMainGoal (mvarId' :: rewrite_result.mvarIds)
    }
    -- Lean.Elab.Tactic.evalTactic (← `(tactic| try done))
    Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
    return ()

-- TODO: Figure out how to extract hypotheses from goal.
-- | this problem is egg-complete.
def not_rewrite : Int := 42
def rewrite_wrong_type : (42 : Nat) = 42 := by { rfl }
def rewrite_correct_type : (42 : Int) = 42 := by { rfl }





-- elab "boiledEgg" "[" rewrites:ident,* "]" : tactic =>  withMainContext  do

-- | test that we can run rewrites
theorem testSuccess : ∀ (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint),
  bint = eint := by
 intros a b c d e aeqa beqd deqe
--  rawEgg [not_rewrite]
--  rawEgg [rewrite_wrong_type]
 rawEgg [beqd, deqe]

#print testSuccess

-- | test that we can run theorems in reverse.
theorem testSuccessRev : ∀ (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint),
  eint = bint := by
 intros a b c d e aeqa beqd deqe
--  rawEgg [not_rewrite]
--  rawEgg [rewrite_wrong_type]
 rawEgg [beqd, deqe]

#print testSuccessRev


theorem testInstantiation
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
 have gh := group_inv h
 have gk := group_inv k
 rawEgg [gh, gk]
 -- TODO: instantiate universally quantified equalities too
-- 

#print testInstantiation

theorem testInstantiation2
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
 rawEgg [group_inv]
#print testInstantiation2


theorem testArrows
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
  rawEgg [group_inv]


theorem assoc_instantiate(G: Type) 
  (mul: G → G → G)
  (assocMul: forall (a b c: G), (mul (mul a b) c) = mul a (mul b c))
  (x y z: G) : mul x (mul y z) = mul (mul x y) z := by {
  rawEgg [assocMul]
}

#print assoc_instantiate


#print assoc_instantiate


#print testArrows

/-
theorem testGoalNotEqualityMustFail : ∀ (a: Nat) (b: Int) (c: Nat) , Nat := by
 intros a b c
 rawEgg []
 sorry
-/

def eof := 1

theorem testInstantiation3
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
 rawEgg [group_inv]
#print testInstantiation3
 -- TODO: instantiate universally quantified equalities too

/-  
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
-/
theorem inv_mul_cancel_left (G: Type) 
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (x: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (invRightX: one = mul x (inv x)): (inv (inv x) = x) := by {
  rawEgg [assocMul, invLeft, mulOne, invRightX]
}
#print inv_mul_cancel_left
