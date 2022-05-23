import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
open Lean Meta Elab Tactic
open Lean.Elab.Term


-- Path to the egg server.
def eggServerPath : String := "/home/bollu/work/egg/egg-tactic-code/json-egg/target/debug/egg-herbie"


elab "myTactic" "[" term,* "]" : tactic =>  do
  let goals <- getGoals
  let target <- getMainTarget
  match target.eq? with
  | none =>  throwError "target {target} is not an equality"
  | some (equalityTermType, equalityLhs, equalityRhs) =>
    let maingoal <- getMainGoal
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
      let out := out ++ m!"-eq.t: {equalityTermType}\n"
      let out := out ++ m!"-eq.lhs: {equalityLhs}\n"
      let out := out ++ m!"-eq.rhs: {equalityRhs}\n"
      let out := out ++ m!"-hypothese of type [eq.t]: {hypsOfEqualityTermType}\n"
      let out := out ++ m!"-hypotheses of [eq.t = eq.t]: {hypsOfEquality}\n"
      -- let out := out ++ m!"-argumentStx: {argumentStx}\n"
      -- let out := out ++ m!"-mainGoal: {maingoal}\n"
      -- let out := out ++ m!"-goals: {goals}\n"
      -- let out := out ++ m!"-target: {target}\n"
      let out := out ++ "\n====\n"
      throwTacticEx `myTactic mvarId out
      return goals

-- theorem test {p: Prop} : (p ∨ p) -> p := by
--   intro h
--   apply Or.elim h
--   trace_state

-- TODO: Figure out how to extract hypotheses from goal.
-- | this problem is egg-complete.
theorem testSuccess : ∀ (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint),
  bint = eint := by
 intros a b c d e aeqa aeqb beqd
 myTactic []
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
