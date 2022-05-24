import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
open Lean Meta Elab Tactic
open Lean.Elab.Term


-- Path to the egg server.
def egg_server_path : String := "/home/bollu/work/egg/egg-tactic-code/json-egg/target/debug/egg-herbie"

#check inferType

#check Lean.Elab.Tactic.elabTerm

structure EggRewrite where
  name: String
  lhs: String
  rhs: String


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


def EggRewrite.toJson (rewr: EggRewrite) :=
  "{"
    ++ surround_quotes "name" ++ " = " ++ surround_quotes rewr.name ++ ","
    ++ surround_quotes "lhs" ++ " = " ++ surround_quotes rewr.lhs ++ ","
    ++ surround_quotes "rhs" ++ " = " ++ surround_quotes rewr.rhs ++
  "}"

instance : ToString EggRewrite where
  toString rewr := rewr.toJson


structure EggRequest where
  target_lhs: String
  target_rhs: String
  rewrites: List EggRewrite

def EggRequest.toJson (e: EggRequest): String :=
  "{"
  ++ surround_quotes "request"  ++  " = " ++ surround_quotes "perform-rewrite" ++ ","
  ++ surround_quotes "target-lhs"  ++  " = " ++ surround_quotes (e.target_lhs) ++ ","
  ++ surround_quotes "target-rhs"  ++  " = " ++ surround_quotes (e.target_rhs) ++ ","
  ++ surround_quotes "rewrites" ++ " = " ++ "[" ++ String.intercalate "," (e.rewrites.map EggRewrite.toJson) ++ "]"
  ++ "}"


def exprToString (lctx: LocalContext) (e: Expr) : Format :=
  -- (repr e)
  if e.isFVar then toString (lctx.getFVar! e).userName else toString e

elab "myTactic" "[" rewrites:term,* "]" : tactic =>  withMainContext  do
  let goals <- getGoals
  let target <- getMainTarget
  match target.eq? with
  | none =>  throwError "target {target} is not an equality"
  | some (equalityTermType, equalityLhs, equalityRhs) =>
    let maingoal <- getMainGoal
    -- | elaborate the given hypotheses as equalities.
    -- These are the rewrites we will perform rewrites with.
    let egg_rewrites : List EggRewrite <- rewrites.getElems.foldlM (init := []) (fun accum rw_stx => withMainContext do
      let rw <-  (Lean.Elab.Tactic.elabTerm rw_stx (Option.none))
      let rw_type <- inferType rw
      match rw_type.eq? with
      | none => throwError "Rewrite |{rw_stx} (term={rw})| must be an equality. Found |{rw} : {rw_type}| which is not an equality"
      | some (rw_eq_type, rw_lhs, rw_rhs) => do
         -- | check that rewrite is of the correct type.
         let is_well_typed <- isExprDefEq rw_eq_type equalityTermType
         if is_well_typed
         then
           let rw_lhs : Expr <- whnf rw_lhs
           let lctx <- getLCtx
           let rw_lhs_decl := LocalContext.findFVar? lctx rw_lhs
           let lhs_name := exprToString lctx rw_lhs
           let rhs_name := exprToString lctx rw_rhs
           dbg_trace "1) rw_stx: {rw_stx} | rw: {rw} | rw_eq_type: {rw_eq_type} | lhs: {lhs_name} | rhs: {rhs_name}"
           let egg_rewrite := { name := toString rw_stx, lhs := toString lhs_name, rhs := toString rhs_name  }
           return (egg_rewrite :: accum)
         else throwError (f!"Rewrite |{rw_stx} (term={rw})| incorrectly equates terms of type |{rw_eq_type}|." ++
         f!" Expected to equate terms of type |{equalityTermType}|")
      -- let tm <- Lean.Elab.Tactic.elabTermEnsuringType rw_stx (Option.some target)
      -- let tm <- Term.elabTerm rw_stx (Option.some target)
      -- return (tm :: accum)
    )


    liftMetaTactic fun mvarId => do
      -- let (h, mvarId) <- intro1P mvarId
      -- let goals <- apply mvarId (mkApp (mkConst ``Or.elim) (mkFVar h))
      let lctx <- getLCtx
      let mctx <- getMCtx
      let hypsOfEqualityTermType <- lctx.foldlM (init := []) (fun accum decl =>  do
          if decl.type == equalityTermType
          then return (decl.userName, decl.type) :: accum
          else return accum)

      let hypsOfEquality <- lctx.foldlM (init := []) (fun accum decl =>  do
          match decl.type.eq? with
          | none => return accum
          | some (eqType', _, _) => do
            let isEqOfCorrectType <- isExprDefEq equalityTermType eqType'
             -- TODO: extract only if eqType = eqType'.
             -- Yes I see the irony.
             if isEqOfCorrectType
             then return (decl.userName, decl.value) :: accum
             else return accum)
      let out := "\n====\n"
      let out := out ++ f!"-eq.t: {equalityTermType}\n"
      let out := out ++ f!"-eq.lhs: {equalityLhs} / {exprToString lctx equalityLhs}\n"
      let out := out ++ f!"-eq.rhs: {equalityRhs} / {exprToString lctx equalityRhs}\n"
      let out := out ++ f!"-hypothese of type [eq.t]: {hypsOfEqualityTermType}\n"
      let out := out ++ f!"-hypotheses of [eq.t = eq.t]: {hypsOfEquality}\n"
      let out := out ++ f!"-hypotheses given of type [eq.t = eq.t]: {egg_rewrites}\n"
      -- let out := out ++ m!"-argumentStx: {argumentStx}\n"
      -- let out := out ++ m!"-mainGoal: {maingoal}\n"
      -- let out := out ++ m!"-goals: {goals}\n"
      -- let out := out ++ m!"-target: {target}\n"
      let out := out ++ "\n====\n"
      -- throwTacticEx `myTactic mvarId out
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
          stdin := IO.Process.Stdio.piped,
          stdout := IO.Process.Stdio.piped
        }
      dbg_trace "3) Spanwed egg server process. Writing stdin..."
      let (stdin, egg_server_process) ← egg_server_process.takeStdin
      stdin.putStr req_json
      dbg_trace "4) Wrote stdin. Flushing..."
      stdin.flush
      dbg_trace "5) Flushed stdin. Setting up stdout..."
      let stdout ← IO.asTask egg_server_process.stdout.readToEnd Task.Priority.dedicated
      dbg_trace "6) Setup stdout. Waiting for exitCode..."
      let exitCode : UInt32 <- egg_server_process.wait
      dbg_trace "7) got exitCode ({exitCode}). Waiting for stdout..."
      let stdout : String <- IO.ofExcept stdout.get
      dbg_trace "8) read stdout."
      -- let stdout : String := "STDOUT"
      dbg_trace ("9)stdout:\n" ++ stdout)
      return goals

-- theorem test {p: Prop} : (p ∨ p) -> p := by
--   intro h
--   apply Or.elim h
--   trace_state

-- TODO: Figure out how to extract hypotheses from goal.
-- | this problem is egg-complete.
def not_rewrite : Int := 42
def rewrite_wrong_type : (42 : Nat) = 42 := by { rfl }
def rewrite_correct_type : (42 : Int) = 42 := by { rfl }


theorem testSuccess : ∀ (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint),
  bint = eint := by
 intros a b c d e aeqa beqd deqe
--  myTactic [not_rewrite]
--  myTactic [rewrite_wrong_type]
 myTactic [beqd, deqe]
 sorry

-- | TODO: figure out how to extract out types like the below.
theorem testInstantiation
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
 myTactic []
 sorry


theorem testGoalNotEqualityMustFail : ∀ (a: Nat) (b: Int) (c: Nat) , Nat := by
 intros a b c
 myTactic []
