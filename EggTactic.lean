import EggTactic.Sexp
import EggTactic.Egraph
import EggTactic.Tracing
import EggTactic.Egraph
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

structure EggConfig where
  explodeMVars : Bool := true
  twoSided : Bool := true
  dumpGraph : Bool := false
  simplifyExprs : Bool := false
  time : Nat := 25
  deriving Repr

instance : Inhabited EggConfig where default := { }

structure EggState where
  ix: Nat := 0
  name2expr: List (Int × Expr) := []
  config : EggConfig
  deriving Inhabited

#check Expr
inductive ExprKind
| ap
| const (c : Name)
| fvar (id : FVarId)
| bvar (id : Nat)
deriving Hashable

abbrev EggM (α: Type) : Type := Egraph.T ExprKind (StateT EggState TermElabM) α

partial def Expr.hashcons (e : Expr) : EggM (Egraph.Ptr `Egraph.Eclass) := do
  match e with
  | .const c [] =>
     let ht : Egraph.HashConsTerm _ :=  { head := ExprKind.const c }
     ht.add
  | .fvar id =>
     let ht : Egraph.HashConsTerm _ :=  { head := ExprKind.fvar id }
     ht.add
  | .app _ _ =>
     let args ← e.getAppArgs.mapM Expr.hashcons
     let fn ← Expr.hashcons e.getAppFn
     -- args : fn
     let args := args.push fn
     let ht : Egraph.HashConsTerm _ :=  { head := ExprKind.ap, args := args }
     ht.add
  | _ => throwError s!"unable to hash cons expr '{e}'"


-- saturate the Egraph with respect to an equality, and return
-- an explanation of why 'lhs' = 'rhs' if possible
def saturate (lhs rhs : Egraph.Ptr `Egraph.Eclass)
  (eq? : Expr) : EggM (Option (Egraph.Explanation ExprKind)) := sorry


declare_syntax_cat eggconfigval
declare_syntax_cat eggconfig

syntax "(" "timeLimit" ":=" num ")" : eggconfigval
syntax "noInstantiation" : eggconfigval
syntax "dump" : eggconfigval
syntax "oneSided" : eggconfigval
syntax "simplify" : eggconfigval
syntax eggconfigval eggconfig : eggconfig
syntax eggconfigval : eggconfig

def runEggM : EggM α → TacticM α := sorry

def Lean.TSyntax.updateEggConfig : TSyntax `eggconfigval → EggConfig → EggConfig
  | `(eggconfigval| noInstantiation ) => λ cfg => { cfg with explodeMVars := false }
  | `(eggconfigval| oneSided ) =>  λ cfg => { cfg with twoSided := false }
  | `(eggconfigval| dump ) =>  λ cfg => { cfg with dumpGraph := true }
  | `(eggconfigval| simplify ) =>  λ cfg => { cfg with simplifyExprs := true }
  | `(eggconfigval| (timeLimit := $n:num) ) => λ cfg => { cfg with time := n.getNat }
  | stx => panic! s!"unknown eggxplosion configuration syntax {stx}"

partial def Lean.TSyntax.getEggConfig : TSyntax `eggconfig → EggConfig
  | `(eggconfig| $v:eggconfigval $r:eggconfig) => v.updateEggConfig r.getEggConfig
  | `(eggconfig| $v:eggconfigval ) => v.updateEggConfig default
  | _ => panic! "unknown eggxplosion config syntax"

/-- runs the explanation to prove that lhs = rhs --/
def runExpl : Egraph.Explanation ExprKind → TacticM Unit := sorry
/-
  -- let mvarId' ← (← getMainGoal).replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
  -- replaceMainGoal (mvarId' :: rewriteResult.mvarIds)
  -- let goal'ty <- inferType (Expr.mvar goal')
  -- trace[EggTactic.egg] (s!"18) new goal: {goal'.name} : {goal'ty}")
  -- replaceMainGoal [goal'] -- replace main goal with new goal + subgoals
-/

elab "eggxplosion" "[" rewriteNames:ident,* "]" c:(eggconfig)? : tactic => withMainContext do
  trace[EggTactic.egg] (s!"0) Running Egg on '{← getMainTarget}'")
  let decls : List LocalDecl := (← getLCtx).decls.toList.filter Option.isSome |>.map Option.get!
  let idsnames := decls.map λ decl => (repr decl.fvarId, decl.userName)
  trace[EggTactic.egg] "\nfvar local decls: {idsnames}\n"

  let (_, goalLhs, goalRhs) ← match (← matchEq? (<- getMainTarget)) with
    | .none => throwError "Egg: target not equality: {<- getMainTarget}"
    | .some eq => pure eq

  let cfg : EggConfig := match c with
    | none =>
      --trace[EggTactic.egg] "did not find config, using default"
      default
    | some cfgSyn => cfgSyn.getEggConfig
  runEggM do
    let lhsCls : Egraph.Ptr `Egraph.Eclass := sorry
    let rhsCls : Egraph.Ptr `Egraph.Eclass := sorry
    -- TODO: implement MonadLift
    let expl? : Option (Egraph.Explanation _) ← do
       for hyp in (← getMainDecl).lctx do
         match (← saturate lhsCls rhsCls hyp.type) with
         | .some explanation => return .some expl
         | .none => continue
       pure .none
    match expl? with
    | .none => throwError "unable to prove"
    | .some expr => runExpl expl
  -- let rewrites ←  (addNamedRewrites (<- getMainGoal) (rewriteNames.getElems.toList)).getRewrites cfg
  -- trace[EggTactic.egg] "simplifying {(← exprToUntypedSexp goalLhs)} {(← exprToUntypedSexp goalRhs)} {rewrites}"

  -- let (simplifiedLhs,simplifiedRhs,simplifiedRewrites,mapping) :=
  --   if cfg.simplifyExprs then
  --      simplifyRequest (← exprToUntypedSexp goalLhs) (← exprToUntypedSexp goalRhs) rewrites
  --   else
  --      (← exprToUntypedSexp goalLhs,← exprToUntypedSexp goalRhs,rewrites,[])
  -- trace[EggTactic.egg] "simplification result {simplifiedLhs} {simplifiedRhs} {simplifiedRewrites}"
  -- trace[EggTactic.egg] "simplification mapping {mapping}"
  -- let explanations := (← runEggRequest (← getMainGoal) eggRequest)
  -- for e in explanations do
  --   trace[EggTactic.egg] (s!"14) applying rewrite explanation {e}")
  --   trace[EggTactic.egg] (s!"14.5) current goal: {(<- getMainGoal).name} : {(<- inferType (Expr.mvar (<- getMainGoal)))}")
  --   let eggRewrite <-
  --     match rewrites.find? (fun rw => rw.name == e.rule) with
  --     | .some rw => pure rw
  --     |  .none => throwTacticEx `eggxplosion (<- getMainGoal) (f!"unknown local declaration {e.rule} in rewrite {e}")
  --   trace[EggTactic.egg] (s!"14.6) found eggRewrite {eggRewrite}\n\twith rw {eggRewrite.rw} : {<- inferType eggRewrite.rw}")
  --   trace[EggTactic.egg] (s!"15) applying rewrite expression eggRewrite: {eggRewrite} to target: {<- getMainTarget}")
  --   let (eggxplanationRw, eggxplanationRwTy) ← e.instantiateEqType eggRewrite
  --   let (mainLhs, mainRhs) ← match (← matchEq? (<- getMainTarget)) with
  --     | .none => throwError "Egg: target not equality: {<- getMainTarget}"
  --     | .some (_, lhs, rhs) => pure (lhs, rhs)
  --   trace[EggTactic.egg] (s!"16) mainLhs     : {mainLhs}")
  --   trace[EggTactic.egg] s!"16) --"
  --   trace[EggTactic.egg] (s!"16) mainRhs     : {mainRhs}")
  --   trace[EggTactic.egg] s!"16) --"
  --   trace[EggTactic.egg] (s!"16) rewrite        : {eggxplanationRw}")
  --   let rewriteType ← inferType eggxplanationRw
  --   trace[EggTactic.egg] (s!"16) rewrite type   : {rewriteType}")
  --   let rewriteResult <- (<- getMainGoal).rewrite
  --       (<- getMainTarget)
  --       eggxplanationRw
  --       (occs := Occurrences.pos [e.position])
  --       -- The rewrite direction here is different from the direction of the
  --       -- explanation! The former is given by egg, the latter is what *we* gave
  --       -- to egg.
  --       (symm := eggRewrite.direction == Backward)

  --   trace[EggTactic.egg] (f!"rewritten to: {rewriteResult.eNew}")
  -- let mvarId' ← (← getMainGoal).replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
  -- replaceMainGoal (mvarId' :: rewriteResult.mvarIds)

    -- let goal'ty <- inferType (Expr.mvar goal')
    -- trace[EggTactic.egg] (s!"18) new goal: {goal'.name} : {goal'ty}")
    -- replaceMainGoal [goal'] -- replace main goal with new goal + subgoals
  -- TODO: replace 'simp' with something that dispatches 'a=a' sanely.
  let _ <- simpGoal (<- getMainGoal) (<- Simp.Context.mkDefault)
  return ()
