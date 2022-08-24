import EggTactic.Sexp
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp
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

builtin_initialize registerTraceClass `EggTactic.egg

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

structure Eggxplanation where
  direction: EggRewriteDirection -- direction of the rewrite
  rule: String -- name of the rewrite rule
  args: Array Expr

instance : ToString Eggxplanation where
  toString expl :=
    let dir := if expl.direction == Forward then "fwd" else "bwd"
    toString f!"(Eggxplanation dir:{dir} rule:{expl.rule} args:{expl.args.toList})"

-- Parse the output egg sexpr as a Lean expr
def parseEggSexprToExpr (s: Sexp): Except String Expr :=
 match s with
 | Sexp.atom x =>
   if x.get 0 == '?'
   then .error s!"Error parsing Eggxplanation {s}: Unexpected metavariable {x}."
   else .error s!"Error parsing Eggxplanation {s}: please pick up expression {x} from the context"
 | Sexp.list _ _ => .error "Error parsing Eggxplanation {s}: List unhandled"

-- | parse a fragment of an explanation into an EggRewrite
def parseExplanation (j: Json) : Except String Eggxplanation := do
  let l <- j.getArr?
  let ty <- l[0]!.getStr?
  dbg_trace "hello!"
  let d <- match ty with
  | "fwd" => pure Forward
  | "bwd" => pure Backward
  | other => throw (toString f!"unknown direction {other} in |{j}")
  let r <- l[1]!.getStr?
  let mut args : Array Expr := #[]
  for arg in l[2:] do
     let sexp ← (parseSingleSexp (← arg.getStr?)).mapError toString
     -- (Rewrite=> <name> <expr>)
     --                   ^^^^^^2
     let sexp := sexp.toList![2]!
     args := args.push (← parseEggSexprToExpr sexp)
  return { direction := d, rule := r, args := args
          : Eggxplanation }

-- | Actually do the IO. This incurs an `unsafe`.
unsafe def unsafePerformIO [Inhabited a] (io: IO a): a :=
  match unsafeIO io with
  | Except.ok a    =>  a
  | Except.error _ => panic! "expected io computation to never fail"

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
  let i := (← get).ix
  dbg_trace s!"addEggRewrite rw:{rw} lhs:{lhs} rhs:{rhs} name:{i}"

  let egg_rewrite := { name := toString i, lhs := lhs, rhs := rhs, rw := rw : EggRewrite }
  modify (fun state => { state with ix := i + 1, name2expr := (i, rw) :: state.name2expr, rewrites := egg_rewrite :: state.rewrites })

def expr_get_forall_bound_vars: Expr -> List Name
| Expr.forallE name ty body _ => name :: expr_get_forall_bound_vars body
| _ => []


def tacticGuard (shouldSucceed?: Bool) (err: MessageData): MetaM Unit :=
  if !shouldSucceed? then throwError err else pure ()

def Array.isSubsetOf [BEq α] (self: Array α) (other: Array α): Bool :=
  self.all (fun x => other.contains x)


-- verify that the expressoin is of the form
-- ∀ x₁, ∀ x₂, ∀ x₃, ... , f(x₁, x₂, ...) = g(x₁, x₂, ...)
-- This is well founded since we reduce on the body of the forall,
-- but lean cannot see this, and hence neds a `partial`.
partial def Lean.Expr.universallyQuantifiedEq? (e: Expr): Bool :=
  -- match e with
  -- | .forallE (body := body) .. =>
  if e.isEq then true
  else if e.isForall
  then e.getForallBody.universallyQuantifiedEq?
  else false


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
  -- NOTE: egg can only handle rewrites where the value of metavars
  -- on the RHS is deduced from the LHS. Thus, we check that
  -- the metavars that occur on the RHS is a subset of the LHS, and
  -- we flip the equality in the symmetric case.
  if rhs.getMVars.isSubsetOf lhs.getMVars then
    addEggRewrite rw (← exprToString lhs) (← exprToString rhs)
  else if lhs.getMVars.isSubsetOf rhs.getMVars then
    addEggRewrite (← mkEqSymm rw) (← exprToString rhs) (← exprToString lhs)
  else
    dbg_trace "ERROR: have equality where RHS has more vars than LHS: (LHS: {lhs}) (RHS: {rhs})"

/-
Create an equality with MVars
-/
def addForallMVarEquality (rw: Expr) (ty: Expr): EggM Unit := do
  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  dbg_trace "**adding forallMVarEquality {rw} : {ty}"
  let (ms, binders, tyNoForall) ← forallMetaTelescope ty
  addBareEquality rw tyNoForall


--  explode an equality with ∀ by creating many variations, from the local context.
-- It is well founded because we destructure the inductive type, but lean is unable to
-- infer this
partial def addForallExplodedEquality_ (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  if let Expr.forallE x xty body _ := ty then do {
  --dbg_trace "**forall is : (FA [{x} : {xty}] {body})"
   withExprsOfType goal xty $ λ xval => do
      -- dbg_trace "**exploding {ty} @ {xval} : {← inferType xval }"
      -- addForallExplodedEquality_ goal rw (←  mkAppM' ty #[xval])
      addForallExplodedEquality_ goal (<- mkAppM' rw #[xval]) (← instantiateForall ty #[xval])
  } else {
    addBareEquality rw ty
  }


-- See `addForallExplodedEquality_`
def addForallExplodedEquality (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  tacticGuard ty.universallyQuantifiedEq? "**expected ∀ ... a = b**"
  dbg_trace "**adding forallExplodedEquality {rw} : {ty}"
  addForallExplodedEquality_ goal rw ty

-- Add an expression into the EggM context, if it is indeed a rewrite
def eggAddExprAsRewrite (goal: MVarId) (rw: Expr) (ty: Expr): EggM Unit := do
  if ty.universallyQuantifiedEq? then
    if ty.isForall then do
        addForallExplodedEquality goal rw ty
        addForallMVarEquality rw ty
    else if ty.isEq then do
        addBareEquality rw ty


-- Add all equalities from the local context
def addAllLocalContextEqualities (goal: MVarId) (goals: List MVarId): EggM Unit :=
  withMVarContext goal do
    dbg_trace "goals: {goals.map fun g => g.name}"
    for decl in (← getLCtx) do
      if decl.toExpr.isMVar && goals.contains (decl.toExpr.mvarId!)
        then continue
      dbg_trace (s!"**processing local declaration {decl.userName}" ++
      s!":= {decl.toExpr} : {← inferType decl.toExpr}")
      -- TODO: call the correct API to resolve metavariables
      -- to enable local declarations such as 'have gh := group_inv h'
      eggAddExprAsRewrite goal (<- reduce decl.toExpr) (<- reduce (← inferType decl.toExpr))


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
def parseEggResponse (goal: MVarId) (responseString: String): MetaM (List Eggxplanation) := do
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
      let explanationE : Except String (List Eggxplanation) := do
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
def runEggRequest (goal: MVarId) (request: EggRequest): MetaM (List Eggxplanation) :=
  runEggRequestRaw request.toJson >>= parseEggResponse goal

-- Add rewrites with known names 'rewriteNames' from the local context of 'goalMVar'
def addNamedRewrites (goalMVar: MVarId)  (rewriteNames: List Ident): EggM Unit :=
  withMVarContext goalMVar do
    dbg_trace " addNamedRewrites {goalMVar.name} {rewriteNames.map toString}"
    for decl in (← getLCtx) do
    -- TODO: find a way to not have to use strings, see how 'simp' does this.
    if !((rewriteNames.map fun ident => ident.getId ).contains decl.userName)
    then continue
    dbg_trace (s!"**processing local declaration {decl.userName}" ++
    s!":= {decl.toExpr} : {← inferType decl.toExpr}")
    eggAddExprAsRewrite  goalMVar decl.toExpr (← inferType decl.toExpr)

elab "rawEgg" "[" rewriteNames:ident,* "]" : tactic => withMainContext do
  let (_, goalLhs, goalRhs) ← match (← matchEq? (<- getMainTarget)) with
      | .none => throwError "Egg: target not equality: {<- getMainTarget}"
      | .some eq => pure eq
      let rewrites ←  (addNamedRewrites (<- getMainGoal) (rewriteNames.getElems.toList)).getRewrites

  let eggRequest := {
      targetLhs := (← exprToString goalLhs),
      targetRhs := (← exprToString goalRhs),
      rewrites := rewrites
      : EggRequest
  }
  let explanations ← runEggRequest (<- getMainGoal) eggRequest
  for e in explanations do
    dbg_trace (s!"14) applying rewrite explanation {e}")
    dbg_trace (s!"14.5) current goal: {(<- getMainGoal).name} : {(<- inferType (Expr.mvar (<- getMainGoal)))}")

    /-
    let some ix := e.rule.toNat?
      | throwTacticEx `rawEgg goalMVar (f!"unknown local declaration {e.rule} in rewrite {e}")
    -/
    let eggRewrite <-
      match rewrites.find? (fun rw => rw.name == e.rule) with
      | .some rw => pure rw
      |  .none => throwTacticEx `rawEgg (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
    dbg_trace (s!"14.6) found eggRewrite {eggRewrite}\n\twith rw {eggRewrite.rw} : {<- inferType eggRewrite.rw}")
    --let rw ← pure eggRewrite.rw
    dbg_trace (s!"15) applying rewrite expression eggRewrite: {eggRewrite} to target: {<- getMainTarget}")
    let rewriteResult <- rewrite (<- getMainGoal) (<- getMainTarget) eggRewrite.rw (symm := e.direction == Backward)
    dbg_trace (s!"16) rewritten to: {rewriteResult.eNew} with proof: {rewriteResult.eqProof}")
    let goal' ← replaceTargetEq (<- getMainGoal) rewriteResult.eNew rewriteResult.eqProof
    let goal'ty <- inferType (Expr.mvar goal')
    dbg_trace (s!"18) new goal: {goal'.name} : {goal'ty}")
    replaceMainGoal (goal' :: rewriteResult.mvarIds) -- replace main goal with new goal + subgoals
  -- TODO: replace 'simp' with something that dispatches 'a=a' sanely.
  let _ <- simpGoal (<- getMainGoal) (<- Simp.Context.mkDefault)
  return ()

-- #check refl
 /-
  let (egg_rewrites , state)  <- rewrites.getElems.foldlM (init := ([], initState))
      (fun xs_and_state stx => do
        let xs := xs_and_state.fst
        let state := xs_and_state.snd
        let (xs', state) <- (addAllLocalContextEqualities (bound := []) equalityTermType xs stx state)
        return (xs', state))

  let explanations : List Eggxplanation <- (liftMetaMAtMain fun mvarId => do
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
      let explanationE : Except String (List Eggxplanation) := do
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
