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




-- Path to the egg server.
def egg_server_path : String := "json-egg/target/debug/egg-herbie"

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


def exprToString (lctx: LocalContext) (e: Expr) : Format :=
  -- (repr e)
  surround_escaped_quotes $
    if e.isFVar then toString (lctx.getFVar! e).userName else toString e

def findMatchingExprs (t : Expr) : TacticM (List Name) :=
  withMainContext do
    let lctx <- getLCtx
    lctx.foldlM (init := []) fun (accum : List Name) (ldecl: LocalDecl) => do
      let ldecl_expr := ldecl.toExpr -- Find the expression of the declaration.
      let ldecl_type <- inferType ldecl_expr
      let res := if ldecl_type == t then ldecl.userName :: accum else accum
      -- This doesn't quite work yet: I need to find a way to unquote it when applying it later
      return res -- why won't return $ if ... work?

def buildRewriteName (rw_stx : Syntax) : TacticM String :=
  let rw_stx_ident := rw_stx.getId
  

partial def addEqualities (equalityTermType : Expr) (accum : List EggRewrite) (rw_stx : Syntax) : TacticM (List EggRewrite) :=
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
       --  let rw_lhs : Expr <- whnf rw_lhs
       --  let rw_lhs_decl := LocalContext.findFVar? lctx rw_lhs
        let lhs_name := exprToString lctx rw_lhs
        let rhs_name := exprToString lctx rw_rhs
        let rw_name <- buildRewriteName rw_stx
          ""
        dbg_trace "1) rw_stx: {rw_stx} | rw: {rw} | rw_eq_type: {rw_eq_type} | lhs: {lhs_name} | rhs: {rhs_name}"
        let egg_rewrite := { name := toString rw_stx_ident, lhs := toString lhs_name, rhs := toString rhs_name  }
        return (egg_rewrite :: accum)
      else throwError (f!"Rewrite |{rw_stx} (term={rw})| incorrectly equates terms of type |{rw_eq_type}|." ++
      f!" Expected to equate terms of type |{equalityTermType}|")
   | none =>
      match rw_type with
        | Expr.forallE n t b _ =>
           let possibleInsts : List Name <- findMatchingExprs t
           let applications : List Syntax <- possibleInsts.mapM λ i:Name =>
             let i_stx := Array.mk [mkIdent i]
             let res := Syntax.mkApp rw_stx i_stx
             return res
           let applyInsts : List (List EggRewrite) <- applications.mapM (addEqualities equalityTermType accum)
           return List.join applyInsts
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
    let egg_rewrites : List EggRewrite <- rewrites.getElems.foldlM (init := []) (addEqualities equalityTermType)
    let explanations : List EggExplanation <- (liftMetaTacticAux fun mvarId => do
      -- let (h, mvarId) <- intro1P mvarId
      -- let goals <- apply mvarId (mkApp (mkConst ``Or.elim) (mkFVar h))
      let lctx <- getLCtx
      let mctx <- getMCtx
      let hypsOfEqualityTermType <- lctx.foldlM (init := []) (fun accum decl =>  do
          if decl.type == equalityTermType
          then return (decl.userName, decl.type) :: accum
          else return accum)

      -- let hypsOfEquality <- lctx.foldlM (init := []) (fun accum decl =>  do
      --     match decl.type.eq? with
      --     | none => return accum
      --     | some (eqType', _, _) => do
      --       let isEqOfCorrectType <- isExprDefEq equalityTermType eqType'
      --        -- TODO: extract only if eqType = eqType'.
      --        -- Yes I see the irony.
      --        if isEqOfCorrectType
      --        -- | accessing decl.value sometimes creates a panic.
      --        then return (decl.userName, decl.value) :: accum
      --        else return accum)
      let out := "\n====\n"
      let out := out ++ f!"-eq.t: {equalityTermType}\n"
      let out := out ++ f!"-eq.lhs: {equalityLhs} / {exprToString lctx equalityLhs}\n"
      let out := out ++ f!"-eq.rhs: {equalityRhs} / {exprToString lctx equalityRhs}\n"
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
        target_lhs := toString (exprToString lctx equalityLhs)
        , target_rhs := toString (exprToString lctx equalityRhs)
        , rewrites := egg_rewrites}
      -- | Invoke accursed magic to send the request.
      let req_json : String := req.toJson
      -- | Steal code from |IO.Process.run|
      dbg_trace "2) sending request |{egg_server_path} {req_json}|"
      let egg_server_process <- IO.Process.spawn
        { cmd := egg_server_path,
          -- stdin := IO.Process.Stdio.piped,
          stdout := IO.Process.Stdio.piped,
          stdin := IO.Process.Stdio.piped,
          -- stdout := IO.Process.Stdio.null,
          stderr := IO.Process.Stdio.null
        }
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
        return (explanation, goals))

    for e in explanations do {
      let lctx <- getLCtx
      dbg_trace (f!"14) aplying rewrite {e}")
      let ldecl <- match lctx.findFromUserName? e.rule with
        | some ldecl => pure ldecl
        | none => throwTacticEx `rawEgg (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
      let ldecl_expr <- if e.direction == Backward then mkEqSymm ldecl.toExpr else pure (ldecl.toExpr)
      -- dbg_trace "explanation: {e} | ldecl: {ldecl.userName}"
      -- | Code stolen from Lean.Elab.Tactic.Rewrite
      let rewrite_result <- rewrite (<- getMainGoal) (<- getMainTarget) ldecl_expr
      let mvarId' ← replaceTargetEq (← getMainGoal) rewrite_result.eNew rewrite_result.eqProof
      replaceMainGoal (mvarId' :: rewrite_result.mvarIds)
    }
    Lean.Elab.Tactic.evalTactic (← `(tactic| try rfl))
    return ()

-- theorem test {p: Prop} : (p ∨ p) -> p := by
--   intro h
--   apply Or.elim h
--   trace_state

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

set_option pp.rawOnError true
theorem testArrows
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
  rawEgg [group_inv]

/-
theorem testGoalNotEqualityMustFail : ∀ (a: Nat) (b: Int) (c: Nat) , Nat := by
 intros a b c
 rawEgg []
 sorry
-/
