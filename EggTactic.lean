/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
open Lean Meta Elab Tactic
open Lean.Elab.Term

elab "myTactic " : tactic => do

  let goals <- getGoals
  let target <- getMainTarget
  let maingoal <- getMainGoal
  liftMetaTactic fun mvarId => do
    -- let (h, mvarId) <- intro1P mvarId
    -- let goals <- apply mvarId (mkApp (mkConst ``Or.elim) (mkFVar h))
    let lctx <- getLCtx
    let mctx <- getMCtx
    -- dbg_trace ("hello: " ++ m!"{(mctx.getDecl $ (goals.get! 0))}")
    throwTacticEx `myTactic mvarId m!"goals: {goals} ;maingoal: {maingoal}; tgt: {target} {mctx}; "
    return goals

-- theorem test {p: Prop} : (p ∨ p) -> p := by
--   intro h
--   apply Or.elim h
--   trace_state

-- TODO: Figure out how to extract hypotheses from goal.
theorem test' : ∀ (a b c : Nat) , a = b := by 
 intros a b c
 myTactic


-- def rewriteTarget (stx : Syntax) (symm : Bool) (config : Rewrite.Config) : TacticM Unit := do
--   Term.withSynthesize <| withMainContext do
--     let e ← elabTerm stx none true
--     let r ← rewrite (← getMainGoal) (← getMainTarget) e symm (config := config)
--     let mvarId' ← replaceTargetEq (← getMainGoal) r.eNew r.eqProof
--     replaceMainGoal (mvarId' :: r.mvarIds)

-- def rewriteLocalDecl2 (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config) : TacticM Unit := do
--   Term.withSynthesize <| withMainContext do
--     let e ← elabTerm stx none true
--     let localDecl ← getLocalDecl fvarId
--     let rwResult ← rewrite (← getMainGoal) localDecl.type e symm (config := config)
--     let replaceResult ← replaceLocalDecl (← getMainGoal) fvarId rwResult.eNew rwResult.eqProof
--     replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

-- def withRWRulesSeq2 (token : Syntax) (rwRulesSeqStx : Syntax) (x : (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
--   let lbrak := rwRulesSeqStx[0]
--   let rules := rwRulesSeqStx[1].getArgs
--   let rbrak := rwRulesSeqStx[2]
--   -- show initial state up to (incl.) `[`
--   withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
--   let numRules := (rules.size + 1) / 2
--   for i in [:numRules] do
--     let rule := rules[i * 2]
--     let sep  := rules.getD (i * 2 + 1) Syntax.missing
--     -- show rule state up to (incl.) next `,`
--     withTacticInfoContext (mkNullNode #[rule, sep]) do
--       -- show errors on rule
--       withRef rule do
--         let symm := !rule[0].isNone
--         let term := rule[1]
--         let processId (id : Syntax) : TacticM Unit := do
--           -- Try to get equation theorems for `id` first
--           let declName ← try resolveGlobalConstNoOverload id catch _ => return (← x symm term)
--           let some eqThms ← getEqnsFor? declName (nonRec := true) | x symm term
--           let rec go : List Name →  TacticM Unit
--             | [] => throwError "failed to rewrite using equation theorems for '{declName}'"
--             | eqThm::eqThms => (x symm (mkIdentFrom id eqThm)) <|> go eqThms
--           go eqThms.toList
--         match term with
--         | `($id:ident)  => processId id
--         | `(@$id:ident) => processId id
--         | _ => x symm term


-- declare_config_elab elabRewriteConfig Rewrite.Config

-- @[tactic evalRewriteSeq2]
-- def evalRewriteSeq2 : Tactic := fun stx => do
--   let cfg ← elabRewriteConfig stx[1]
--   let loc   := expandOptLocation stx[3]
--   withRWRulesSeq2 stx[0] stx[2] fun symm term => do
--     withLocation loc
--       (rewriteLocalDecl2 term symm · cfg)
--       (rewriteTarget term symm cfg)
--       (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

-- end Lean.Elab.Tactic


-- abbrev TacticM := ReaderT Context $ StateRefT State TermElabM
-- abbrev Tactic  := Syntax → TacticM Unit

-- structure LocalContext where
--   fvarIdToDecl : PersistentHashMap FVarId LocalDecl := {}
--   decls        : PersistentArray (Option LocalDecl) := {}
--   deriving Inhabited

-- throwTacticEx `rewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
-- match (← matchEq? heqType) with
