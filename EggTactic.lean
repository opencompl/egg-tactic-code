import EggTactic.Sexp
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson

open Lean Elab Meta Tactic Term
open IO
open System

-- Path to the egg server.
def egg_server_path : String := 
  "json-egg/target/debug/egg-herbie"

structure EggRewrite where
  name: String
  lhs: String
  rhs: String
  rw: Expr

instance : Inhabited EggRewrite where
  default := EggRewrite.mk "default" "default" "default" default

inductive EggRewriteDirection where
  | Forward
  | Backward
  deriving Inhabited, DecidableEq

open EggRewriteDirection

structure EggExplanation where
  direction: EggRewriteDirection -- direction of the rewrite
  rule: String -- name of the rewrite rule
  args: Array Expr

instance : ToString EggExplanation where
  toString expl :=
    let dir := if expl.direction == Forward then "fwd" else "bwd"
    toString f!"[{dir}, {expl.rule}]"

  
def eggParseExpr (s: String): Except SexpError Expr :=
  match parseSexp s with 
  | .error err => .error err
  | .ok v => 

-- | parse a fragment of an explanation into an EggRewrite
def parseExplanation (j: Json) : Except String EggExplanation := do
  let l <- j.getArr?
  let ty <- l[0]!.getStr?
  let d <- match ty with
  | "fwd" => pure Forward
  | "bwd" => pure Backward
  | other => throw (toString f!"unknown direction {other} in |{j}")
  let r <- l[1]!.getStr?
  let mut args : Array Expr := #[]
  for arg in l[2:] do 
     args := args.push (←  eggParseExpr arg)
     pure ()
  return { direction := d, rule := r, args := args : EggExplanation }

-- | Actually do the IO. This incurs an `unsafe`.
unsafe def unsafePerformIO [Inhabited a] (io: IO a): a :=
  match unsafeIO io with
  | Except.ok a    =>  a
  | Except.error e => panic! "expected io computation to never fail"

-- | Circumvent the `unsafe` by citing an `implementedBy` instance.
@[implementedBy unsafePerformIO]
def performIO [Inhabited a] (io: IO a): a := Inhabited.default


def surroundQuotes (s: String): String :=
 "\"" ++ s ++ "\""
def surround_escaped_quotes (s: String): String :=
 "\\\"" ++ s ++ "\\\""


def EggRewrite.toJson (rewr: EggRewrite) :=
  "{"
    ++ surroundQuotes "name" ++ ":" ++ surroundQuotes rewr.name ++ ","
    ++ surroundQuotes "lhs" ++ ":" ++ surroundQuotes rewr.lhs ++ ","
    ++ surroundQuotes "rhs" ++ ":" ++ surroundQuotes rewr.rhs ++
  "}"

instance : ToString EggRewrite where
  toString rewr := rewr.toJson


structure EggRequest where
  targetLhs: String
  targetRhs: String
  rewrites: List EggRewrite

def EggRequest.toJson (e: EggRequest): String :=
  "{"
  ++ surroundQuotes "request"  ++  ":" ++ surroundQuotes "perform-rewrite" ++ ","
  ++ surroundQuotes "target-lhs"  ++  ":" ++ surroundQuotes (e.targetLhs) ++ ","
  ++ surroundQuotes "target-rhs"  ++  ":" ++ surroundQuotes (e.targetRhs) ++ ","
  ++ surroundQuotes "rewrites" ++ ":" ++ "[" ++ String.intercalate "," (e.rewrites.map EggRewrite.toJson) ++ "]"
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


/-
convert this expression into a string, along with the names of the
bound variables.
-/
def exprToString (e: Expr): MetaM String :=   
match e with 
  | Expr.const name levels => pure (name.toString)
  | Expr.bvar ix => throwError s!"expected no bound variables, we use locally nameless!"
  | Expr.fvar id => pure (id.name.toString)
  | Expr.mvar id => pure ("?" ++ (id.name.toString))
  | Expr.lit (.natVal n)=> pure (toString n)
  | Expr.app  l r => do 
     let lstr <- exprToString l
     let rstr <- exprToString r
     pure $ "(ap " ++ lstr ++ " " ++ rstr ++ ")"
  | _ => throwError s!"unimplemented expr_to_string ({e.ctorName}): {e}"


def Lean.Expr.getMVars (e: Expr) (arr: Array MVarId := #[]): Array MVarId := 
match e with 
  | Expr.mvar id => arr.push id
  | Expr.app l r => 
     r.getMVars (l.getMVars arr)
  | _ => arr

structure EggState where
  ix: Nat := 0
  name2expr: List (Int × Expr) := []
  rewrites: List EggRewrite := []
  deriving Inhabited

abbrev EggM (α: Type) := StateT EggState TermElabM α

-- Lens s t a b = forall f. Profunctor f => (p a b) -> (p s t)
#check EggState.ix
def EggM.getRewrites (egg: EggM Unit): TermElabM (List EggRewrite) := do 
  pure (← egg.run default).snd.rewrites

-- Find expressions of a given type in the local context
def withExprsOfType (g: MVarId) (t : Expr) (f: Expr → EggM Unit): EggM Unit := do
   withMVarContext g do
    let lctx <- getLCtx
    for ldecl in lctx do 
      let ldecl_type <- inferType ldecl.toExpr
      if (← isExprDefEq ldecl_type t) then f ldecl.toExpr



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


partial def addEggRewrite (rw: Expr) (lhs: String) (rhs: String): EggM Unit := do
  dbg_trace s!"MK_EGG_REWRITE {rw}"
  let i := (← get).ix
  let egg_rewrite := { name := toString i, lhs := lhs, rhs := rhs, rw := rw : EggRewrite }
  modify (fun state => { state with ix := i + 1, name2expr := (i, rw) :: state.name2expr, rewrites := egg_rewrite :: state.rewrites })

def expr_get_forall_bound_vars: Expr -> List Name 
| Expr.forallE name ty body _ => name :: expr_get_forall_bound_vars body 
| _ => []

-- | disgusting. Please fix to a real parser later @andres
partial def parseNat (s: String) (counter: Nat := 100) : Option Nat :=
  if toString counter == s
  then some counter
  else if counter == 0 then none else parseNat s (counter - 1)


def tacticGuard (shouldSucceed?: Bool) (err: MessageData): MetaM Unit := 
  if !shouldSucceed? then throwError err else pure ()

def Array.isSubsetOf [BEq α] (self: Array α) (other: Array α): Bool :=
  self.all (fun x => other.contains x)


/-
Create a regular equality of the form lhs = rhs
-/
def addBareEquality (rw: Expr) (ty: Expr): EggM Unit := do
  dbg_trace "**adding bareEquality {rw} : {ty}"
  -- Check if the lhs has all the mvars of the rhs
  let (lhs, rhs)  ←
      match (← matchEq? ty) with
      | some (_, lhs, rhs) => 
          pure (lhs, rhs) 
      | none => throwError f!"**expected type to be equality: {ty}"
  if rhs.getMVars.isSubsetOf lhs.getMVars then
    addEggRewrite rw (← exprToString lhs) (← exprToString rhs)
  else 
    dbg_trace "**have equality where RHS has more vars than LHS: {ty}"

/-
Create an equality with MVars
-/
def addForallMVarEquality (rw: Expr) (ty: Expr): EggM Unit := do 
  tacticGuard ty.isForall "**expected ∀ at mvar equality"
  dbg_trace "**adding forallMVarEquality {rw} : {ty}"
  let (ms, binders, tyNoForall) ← forallMetaTelescope ty
  addBareEquality rw tyNoForall


--  explode an equality with ∀ by creating many variations, from the local context.
-- It is well founded because we destructure the inductive type, but lean is unable to
-- infer this
partial def addForallExplodedEquality_ (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do 
  if let Expr.forallE x xty body _ := ty then do {
  dbg_trace "**forall is : (FA [{x} : {xty}] {body})"
   withExprsOfType goal xty $ λ xval => do 
      -- dbg_trace "**exploding {ty} @ {xval} : {← inferType xval }"
      -- addForallExplodedEquality_ goal rw (←  mkAppM' ty #[xval])
      addForallExplodedEquality_ goal rw (← instantiateForall ty #[xval])
  } else {
    addBareEquality rw ty
  }


-- See `addForallExplodedEquality_`
def addForallExplodedEquality (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do 
  tacticGuard ty.isForall "**expected ∀ at exploded equality"
  dbg_trace "**adding forallExplodedEquality {rw} : {ty}"
  addForallExplodedEquality_ goal rw ty

-- Add an expression into the EggM context.
def addExpr (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
   if ty.isForall then do
     addForallExplodedEquality_ goal rw ty
     addForallMVarEquality rw ty
   else if ty.isEq then do
     addBareEquality rw ty

-- Add all equalities from the local context 
def addAllLocalContextEqualities (goal: MVarId): EggM Unit := 
  withMVarContext goal do
    for decl in (← getLCtx) do 
      dbg_trace "**processing local declaration {decl.userName} := {decl.toExpr} : {← inferType decl.toExpr}"
      addExpr goal decl.toExpr (← inferType decl.toExpr)



-- Do the dirty work of sending a string, and reading the string out from stdout
def runEggRequestRaw (requestJson: String): MetaM String := do
    dbg_trace "sending request:\n{requestJson}"
    let eggProcess <- IO.Process.spawn
      { cmd := egg_server_path,
        -- stdin := IO.Process.Stdio.piped,
        stdout := IO.Process.Stdio.piped,
        stdin := IO.Process.Stdio.piped,
        -- stdout := IO.Process.Stdio.null,
        stderr := IO.Process.Stdio.null
      }
    FS.writeFile s!"/tmp/egg.json" requestJson
    dbg_trace "3) Spanwed egg server process. Writing stdin..."
    let (stdin, eggProcess) ← eggProcess.takeStdin
    stdin.putStr requestJson
    dbg_trace "5) Wrote stdin. Setting up stdout..."
    let stdout ← IO.asTask eggProcess.stdout.readToEnd Task.Priority.dedicated
    dbg_trace "6) Setup stdout. Waiting for exitCode..."
    let exitCode : UInt32 <- eggProcess.wait
    dbg_trace "7) got exitCode ({exitCode}). Waiting for stdout..."
    let stdout : String <- IO.ofExcept stdout.get
    -- dbg_trace "8) read stdout."
    -- let stdout : String := "STDOUT"
    dbg_trace ("9)stdout:\n" ++ stdout)
    return stdout


-- parse the response, given the response as a string
def parseEggResponse (goal: MVarId) (responseString: String): MetaM (List EggExplanation) := do
    let outJson : Json <- match Json.parse responseString with
      | Except.error e => throwTacticEx `rawEgg goal e
      | Except.ok j => pure j
    dbg_trace ("10)stdout as json:\n" ++ (toString outJson))
    let responseType := (outJson.getObjValD "response").getStr!
    dbg_trace ("11)stdout response: |" ++ responseType ++ "|")
    if responseType == "error"
    then throwTacticEx `rawEgg goal (toString outJson)
    else
      dbg_trace "12) Creating explanation..."
      -- This whole thing is in an Except beacause everything in Json
      -- is written relative to Except, and not a general MonadError :(
      let explanationE : Except String (List EggExplanation) := do
         -- extract explanation field from response
         let expl <- (outJson.getObjVal? "explanation")
         -- cast field to array
         let expl <- Json.getArr? expl
         -- map over each element into an explanation
         let expl <- expl.mapM parseExplanation
         return expl.toList
      let explanation <- match explanationE with
        | Except.error e => throwTacticEx `rawEgg goal (e)
        | Except.ok v => pure v
      dbg_trace ("13) explanation: |" ++ String.intercalate " ;;; " (explanation.map toString) ++ "|")
      return explanation

-- High level wrapped aroung runEggRequestRaw that is well-typed, and returns the 
-- list of explanations
def runEggRequest (goal: MVarId) (request: EggRequest): MetaM (List EggExplanation) :=
  runEggRequestRaw request.toJson >>= parseEggResponse goal



elab "rawEgg" "[" rewrites:ident,* "]" : tactic => withMainContext do
  let goalMVar <- getMainGoal
  let target <- getMainTarget
  let (goalType, goalLhs, goalRhs) ← match (← matchEq? target) with
      | .none => throwError "Egg: target not equality: {target}"
      | .some eq => pure eq
  let rewrites ← (addAllLocalContextEqualities  (← getMainGoal)).getRewrites
  let eggRequest := { 
      targetLhs := (← exprToString goalLhs),
      targetRhs := (← exprToString goalRhs),
      rewrites := rewrites
      : EggRequest
  }
  let explanations ← runEggRequest goalMVar eggRequest
  for e in explanations do {
    let lctx <- getLCtx
    dbg_trace (s!"14) aplying rewrite explanation {e}")
    let ix : Int ← match parseNat e.rule with
      | some ix => pure ix
      | none => throwTacticEx `rawEgg goalMVar (f!"unknown local declaration {e.rule} in rewrite {e}")
    let eggRewrite := rewrites.get! ix
    let rw ← if e.direction == Backward then mkEqSymm eggRewrite.rw else pure eggRewrite.rw
    dbg_trace (s!"**applying rewrite expression: {eggRewrite}")
    dbg_trace (s!"**applying rewrite expression: {rw}")
    let rewriteResult <- rewrite goalMVar target rw
    dbg_trace (s!"**rewritten to: {rewriteResult.eNew}")
    let goal' ← replaceTargetEq goalMVar rewriteResult.eNew rewriteResult.eqProof
    -- dbg_trace (s!"** new goal: {goal'}")
    replaceMainGoal (goal' :: rewriteResult.mvarIds) -- replace main goal with new goal + subgoals
  }
  return ()
      
 /-
  let (egg_rewrites , state)  <- rewrites.getElems.foldlM (init := ([], initState)) 
      (fun xs_and_state stx => do 
        let xs := xs_and_state.fst 
        let state := xs_and_state.snd 
        let (xs', state) <- (addAllLocalContextEqualities (bound := []) equalityTermType xs stx state)
        return (xs', state))
  
  let explanations : List EggExplanation <- (liftMetaMAtMain fun mvarId => do
    let lctx <- getLCtx
    let mctx <- getMCtx
    let hypsOfEqualityTermType <- lctx.foldlM (init := []) (fun accum decl =>  do
        if decl.type == equalityTermType
        then return (decl.userName, decl.type) :: accum
        else return accum)

    let out := "\n====\n"
    let lhs_str : Format <- exprToString equalityLhs
    let rhs_str : Format <- exprToString equalityRhs
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
      targetLhs := toString (lhs_str)
      , targetRhs := toString (rhs_str)
      , rewrites := egg_rewrites}
    -- | Invoke accursed magic to send the request.
    let req_json : String := req.toJson
    -- | Steal code from |IO.Process.run|
    dbg_trace "2) sending request:---\n {egg_server_path}\n{req_json}\n---"
    let eggProcess <- IO.Process.spawn
      { cmd := egg_server_path,
        -- stdin := IO.Process.Stdio.piped,
        stdout := IO.Process.Stdio.piped,
        stdin := IO.Process.Stdio.piped,
        -- stdout := IO.Process.Stdio.null,
        stderr := IO.Process.Stdio.null
      }
    FS.writeFile s!"/tmp/egg.json" req_json
    dbg_trace "3) Spanwed egg server process. Writing stdin..."
    let (stdin, eggProcess) ← egg_server_process.takeStdin
    stdin.putStr req_json
    dbg_trace "5) Wrote stdin. Setting up stdout..."
    let stdout ← IO.asTask eggProcess.stdout.readToEnd Task.Priority.dedicated
    dbg_trace "6) Setup stdout. Waiting for exitCode..."
    let exitCode : UInt32 <- eggProcess.wait
    dbg_trace "7) got exitCode ({exitCode}). Waiting for stdout..."
    let stdout : String <- IO.ofExcept stdout.get
    -- dbg_trace "8) read stdout."
    -- let stdout : String := "STDOUT"
    dbg_trace ("9)stdout:\n" ++ stdout)
    let outJson : Json <- match Json.parse stdout with
      | Except.error e => throwTacticEx `rawEgg mvarId e
      | Except.ok j => pure j
    dbg_trace ("10)stdout as json:\n" ++ (toString outJson))
    let responseType := (outJson.getObjValD "response").getStr!
    dbg_trace ("11)stdout response: |" ++ responseType ++ "|")
    if responseType == "error"
    then
      throwTacticEx `rawEgg mvarId (toString outJson)
    else
      dbg_trace "12) Creating explanation..."
      let explanationE : Except String (List EggExplanation) := do
         -- extract explanation field from response
         let expl <- (outJson.getObjVal? "explanation")
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
  dbg_trace (f!"14) aplying rewrite explanation {e}")
    let name : String := e.rule
    let ldecl_expr <- match (parseNat 100 name) >>= (state.findExpr) with
    | some e => pure e
    | none => do 
       throwTacticEx `rawEgg (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
  let ldecl_expr <- if e.direction == Backward then mkEqSymm ldecl_expr else pure ldecl_expr
  dbg_trace (f!"15) aplying rewrite expression {ldecl_expr}")
  let rewriteResult <- rewrite (<- getMainGoal) (<- getMainTarget) ldecl_expr
  dbg_trace (f!"rewritten to: {rewriteResult.eNew}")
  let mvarId' ← replaceTargetEq (← getMainGoal) rewriteResult.eNew rewriteResult.eqProof
  replaceMainGoal (mvarId' :: rewriteResult.mvarIds)
}
-- Lean.Elab.Tactic.evalTactic (← `(tactic| try done))
Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
return ()
-/

-- TODO: Figure out how to extract hypotheses from goal.
-- | this problem is egg-complete.
-- def not_rewrite : Int := 42
-- def rewrite_wrong_type : (42 : Nat) = 42 := by { rfl }
-- def rewrite_correct_type : (42 : Int) = 42 := by { rfl }


theorem testSuccess0 (anat: Nat) (bnat: Nat) (H: anat = bnat): anat = bnat := by {
  intros;
  rawEgg []
}



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
  
}
--   rawEgg [assocMul, invLeft, mulOne, invRightX]
-- }

#print inv_mul_cancel_left
