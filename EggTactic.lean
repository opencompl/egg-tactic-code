import EggTactic.Sexp
import EggTactic.Tracing
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Simp
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Elab.Tactic.Config
import Lean.Meta.AppBuilder -- mEqSymm
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



abbrev Ptr := UInt64
abbrev RepPtr := UInt64

inductive EqProof where
| leanProof (e : Expr)
| rfl
| sym_ (prf : EqProof)
| sequence_ (prf1 prf2 : EqProof)
| replace (oldExpr newExpr : Expr) (prf : EqProof)
deriving BEq, Hashable

def parenIf : Bool → Format → Format
| true, f => f.paren
| false, f => f

-- sym a ; b -> sym (a ; b) ?
instance : ToFormat EqProof where
  format e :=
  let rec go : Nat → EqProof → Format -- surrounding precedence. higher binds tighter
  | _, .leanProof e => format e
  | _i, .rfl => "rfl"
  | _i, .sym_ p => f!"sym {go 100 p}"
  | i, .sequence_ p1 p2 => parenIf (i > 0) f!"{go 0 p1}; {go 0 p2}"
  | _i, .replace _ _ prf => f!"replace {go 100 prf}"
  go 0 e -- start with minimum: 0


instance : Inhabited EqProof where
  default := EqProof.leanProof <| Expr.lit <| .strVal "DEFAULT"

/- smart constructor for sequencing proofs -/
def EqProof.sequence : EqProof → EqProof → EqProof
| .rfl, x => x
| x, .rfl => x
| x, y => .sequence_ x y

/-- smart constructor for taking symmetric version of proof --/
def EqProof.sym : EqProof → EqProof
| .rfl => .rfl
| .sym_ x => x
| x => .sym_ x


-- | unrolled version of Expr with internal nodes
-- replaced with α
inductive ExprF (α : Type) where
| const (declName : Name) (us : List Level)
| fvar (fvarId : FVarId)
| app (f : α) (arg : α)
| lit (lit : Literal)
deriving BEq, Hashable, Inhabited

-- | TODO: consider using `Repr`.
instance [ToFormat α] : ToFormat (ExprF α) where
  format
  | .const declName us => f!"const {format declName} {format us}"
  | .fvar fvarId => f!"{repr fvarId}"
  | .app f arg => f!"{format f} {format arg}"
  | .lit l => s!"{repr l}"

def ExprF.mapM {m : Type → Type} [Monad m] (act : α → m β) : ExprF α → m (ExprF β)
| .const declName us => return .const declName us
| .fvar fvarId => return .fvar fvarId
| .app f arg => do
  return .app (← act f) (← act arg)
| .lit l => return .lit l

def ExprF.map (act : α → β) (e : ExprF α) : (ExprF β) :=
  Id.run <| e.mapM <| pure ∘ act

def ExprF.forM [Monad m] (act : α → m Unit) : ExprF α → m Unit
| .const _ _ => pure ()
| .fvar _ => pure ()
| .app f arg => do
  _ ← act f
  _ ← act arg
| .lit _ => pure ()

def ExprF.foldlMGo [Monad m] (act : α → m β) (arr : Array β) : ExprF α → m (Array β)
| .const _ _ => pure arr
| .fvar _ => pure arr
| .app f arg => do
  let arr := arr.push (← act f)
  let arr := arr.push (← act arg)
  return arr
| .lit _ => pure arr

def ExprF.foldlM [Monad m] (act : α → m β) (e : ExprF α) : m (Array β) :=
   e.foldlMGo act #[]

abbrev ExprHashCons := ExprF Ptr

/--
convert a natural into a sequence of bigrams of vowel-consonant
that is easy to pronounce. If ` is true, then print a '-'
before we start the string. -/
partial def NatToName (n : Nat) : String :=
  if n == 0 then ""
  else Id.run do
    let cs := "bcdfghjklmnpqrstvwxzy";
    let vs := "aeiou";
    let mut n := n
    let mut chunk := 0
    let mut out : String := ""
    while n > 0 do
        let digit : Nat := n % (cs.length * vs.length)
        let cix : Nat := digit % cs.length
        let vix := digit / cs.length
        out := out ++ s!"{cs.get ⟨cix⟩}{vs.get ⟨vix⟩}"
        n := n / (cs.length * vs.length)
        chunk := chunk + 1
        if chunk == 2 && n > 0then
          out := out ++ "-"
          chunk := 0
    return out

def Ptr.toString (p: Ptr) : String := Id.run do
  s!"0x{NatToName p.toNat}"

instance : ToString Ptr where
  toString := Ptr.toString

/-- Structure for pretty printing indent levels -/
structure Indent where
  depth : Nat := 0
deriving Inhabited, DecidableEq

def Indent.increment (d: Indent) : Indent where
  depth := d.depth + 1

instance : ToString Indent where
  toString d := Id.run do
    let rec go (s : String) : Nat → String
    | 0 => s
    | n' + 1 =>  go (s ++ " │") n'
    go "" d.depth

instance : ToMessageData Indent where
  toMessageData d := toString d


structure Egraph where
  rep2canon : HashMap RepPtr ExprHashCons := {}-- must be represenattive pointer.
  rep2users : HashMap RepPtr (Array Ptr) := {} -- must be representative pointer.
  ptr2ptr : HashMap Ptr (Ptr × EqProof) := {}
  canon2ptr : HashMap ExprHashCons Ptr := {}
  pending : List (Ptr × Ptr × EqProof) := [] -- pending updates.
  ptrGensym : Ptr := 1337

instance : Inhabited Egraph where
  default := {}


structure EggState where
  ix: Nat := 0
  name2expr: List (Int × Expr) := []
  config : EggConfig
  egraph : Egraph
  indent : Indent -- indent level for tracing.
  deriving Inhabited

abbrev EggM (α: Type) : Type :=
  StateT EggState TacticM α

def getEgraph : EggM Egraph := do return (← get).egraph

def viewEgraph (f : Egraph → EggM α): EggM α := getEgraph >>= f

def modifyGetEgraph (f : Egraph → α × Egraph) : EggM α :=
  modifyGet fun s =>
    let (a, egraph) := f s.egraph
    (a, { s with egraph := egraph })

def modifyGetEgraphM (f : Egraph → EggM (α × Egraph)) : EggM α := do
  let s ← get
  let (a, egraph) ← f s.egraph
  set { s with egraph := egraph  }
  return a

def modifyEgraphM (f : Egraph → EggM Egraph) : EggM Unit :=
  modifyGetEgraphM fun g => do return ((), ← f g)

def getIndent : EggM Indent := do return (← get).indent
def getIndent2 : EggM Indent := do return (← get).indent.increment
def withIndent (m : EggM α) : EggM α := fun s => do
  let indent := s.indent
  let (a, s) ← m { s with indent := indent.increment }
  let s := { s with indent := indent }
  return (a, s)

-- TODO: write modifyEgraph, modifyEgraphWith

partial def ptr2repWithProof (p : Ptr) : EggM (RepPtr × EqProof) := withIndent do
  let egraph := (← get).egraph
  let (parent, p2parent) := egraph.ptr2ptr.find! p
  trace[EggTactic.egg] "{← getIndent}ptr2rep p:{p}=>"
  if parent == p then
    trace[EggTactic.egg] "{←getIndent2}<=parent:{parent} prf:{p2parent}"
    return (p, p2parent)
  else
    let (rep, parent2rep) ← ptr2repWithProof parent
    let prf := EqProof.sequence p2parent parent2rep
    let egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert p (rep, prf) }
    trace[EggTactic.egg] "{←getIndent2}<=parent:{parent} prf:{prf}"
    modifyGet fun s => ((rep, prf), { s with egraph := egraph })

def ptr2rep (p : Ptr) : EggM RepPtr := do
  return (← ptr2repWithProof p).fst


def egraphDeref : Ptr → EggM ExprHashCons
| p => do return (← get).egraph.rep2canon.find! (← ptr2rep p)

def canonicalizeHashCons (ehc : ExprHashCons) : EggM ExprHashCons := withIndent do
  trace[EggTactic.egg] "{←getIndent}canonicalize {ehc}"
  let out ← ehc.mapM ptr2rep
  trace[EggTactic.egg] "{←getIndent2}{out}"
  return out

def ExprHashCons.replaceAllUsesWith (old new : Ptr) (ehc : ExprHashCons) : ExprHashCons :=
  ehc.map (fun ptr => if ptr == old then new else ptr )

-- | TODO: write a fusion law so we don't traverse structure twice?
def ExprF.toExpr : ExprF Expr → Expr
| .const declName us => .const declName us
| .app f arg => .app f arg
| .lit l => .lit l
| .fvar fvarId => .fvar fvarId

mutual -- TOEXPR
partial def ExprHashCons.toExpr (eh : ExprHashCons) : EggM Expr := do
  return ExprF.toExpr (← eh.mapM Ptr.toExpr)

partial def Ptr.toExpr (ptr : Ptr) : EggM Expr := do
  ExprHashCons.toExpr (← egraphDeref ptr)
end -- TOEXPR

def egraphAppendUser (userPtr : Ptr) (usedPtr : RepPtr)
  (g : Egraph) : EggM Egraph := withIndent do
  trace[EggTactic.egg] "{←getIndent}appendUser {userPtr} uses {usedPtr}=>"
  let users := g.rep2users.find! usedPtr
  return { g with rep2users := g.rep2users.insert usedPtr (users.push userPtr) }

def egraphAddHashCons (ehc : ExprHashCons) : EggM Ptr := withIndent do
  trace[EggTactic.egg] "{←getIndent}+hashcons 'ehc:{ehc}'=>" -- TODO: add 'Indent'
  modifyGetEgraphM fun egraph => do
  let mut egraph := egraph
  let canon ← canonicalizeHashCons ehc
  match egraph.canon2ptr.find? canon with
  | .none =>
      trace[EggTactic.egg] "{←getIndent2}egraph[canon] → .none" -- TODO: add 'Indent'
      let canonPtr : Ptr := egraph.ptrGensym
      egraph := { egraph with ptrGensym := egraph.ptrGensym + 1 }
      trace[EggTactic.egg] "{←getIndent2}egraph[canon] ← {canonPtr}" -- TODO: add 'Indent'
      -- 1. update `rep2canon`
      egraph := { egraph with rep2canon := egraph.rep2canon.insert canonPtr canon }
      -- 2. update `rep2users`.
      for used in  (← canon.foldlM pure) do
        egraph ← egraphAppendUser (userPtr := canonPtr) (usedPtr := used) egraph
      -- 3. update `ptr2ptr`
      egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert canonPtr (canonPtr, .rfl) }
      -- 4. update `canon2ptr`
      egraph := { egraph with canon2ptr := egraph.canon2ptr.insert canon canonPtr }
      return (canonPtr, egraph)
  | .some ptr =>
      trace[EggTactic.egg] "{←getIndent2}egraph[canon] → .some '{ptr}'"
      trace[EggTactic.egg] "{←getIndent2}<='{ptr}'"
      return (ptr, egraph)

open Lean Elab Meta Tactic in
mutual
partial def egraphAddExpr (e : Expr) : EggM (Option Ptr) := withIndent do
  trace[EggTactic.egg] "{←getIndent}+expr {e}=>"
  let out ← egraphAddExprGo e
  trace[EggTactic.egg] "{←getIndent2}<={out}"
  return out
partial def egraphAddExprGo : Expr → EggM (Option Ptr)
| .const declName ls =>
  egraphAddHashCons <| ExprF.const declName ls
| .fvar id =>
  egraphAddHashCons <| ExprF.fvar id
| .app f arg => do
  let fh ←
    match ← egraphAddExpr f with
    | .some f => pure f
    | .none => return .none
  let argh ←
    match ← egraphAddExpr arg with
    | .some arg => pure arg
    | .none => return .none
  egraphAddHashCons <| .app fh argh
| .lit name =>
  egraphAddHashCons <| .lit name
| _ => return .none
end


mutual -- UNITE
-- | Calling unite will only enque a unite. must call propagate()
partial def egraphEnqueueUnite (lhs rhs : Ptr) (lhs2rhs : EqProof) : EggM Unit :=
  withIndent do
    trace[EggTactic.egg] "{← getIndent}∪ lhs:{lhs} rhs:{rhs}=>"
    trace[EggTactic.egg] "{← getIndent2}lhs2rhs:{lhs2rhs}"
    modifyEgraphM fun egraph => do
      return { egraph with pending := (lhs, rhs, lhs2rhs) :: egraph.pending }

partial def egraphPropagate : EggM Unit := do
  let _ ← egraphPropagateGo
  if not (← get).egraph.pending.isEmpty then
    egraphPropagate


partial def egraphPropagateGo : EggM Unit :=
  withIndent <| modifyEgraphM fun egraph => do
    -- TODO: wrap this up in a pop() call.
    match egraph.pending with
    | [] => return egraph
    | (lhs, rhs, lhs2rhs) :: pending => withIndent do
      trace[EggTactic.egg] "{← getIndent}propagate lhs:{lhs} rhs:{rhs}"
      trace[EggTactic.egg] "{← getIndent}lhs2rhs:{lhs2rhs}=>"
      let mut egraph := egraph
      -- 5. pending : List (Ptr × Ptr × EqProof) -- pending updates.
      egraph := { egraph with pending := pending } -- pop
      let (lhsrep, lhs2lhsrep) ← ptr2repWithProof lhs
      let (rhsrep, rhs2rhsrep) ← ptr2repWithProof rhs
      let rhsrep2rhs := rhs2rhsrep.sym
      let rhs2lhs := lhs2rhs.sym
      let rhsrep2lhsrep :=
         (rhsrep2rhs.sequence rhs2lhs).sequence lhs2lhsrep
      -- merge rhs into lhs.
      -- 3. ptr2ptr : HashMap Ptr (Ptr × EqProof)
      trace[EggTactic.egg] "{← getIndent2} uniting rhs:{rhsrep} into lhsrep:{lhsrep}"
      trace[EggTactic.egg] "{← getIndent2}propagate prf: {rhsrep2lhsrep}"
      egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert rhsrep (lhsrep, rhsrep2lhsrep) }
      -- 1. rep2canon : HashMap RepPtr ExprHashCons -- must be represenattive pointer.
      egraph := { egraph with rep2canon := egraph.rep2canon.erase rhsrep }
      -- 2. rep2users : HashMap RepPtr (Array Ptr) -- must be representative pointer.
      let rhsUsers := egraph.rep2users.find! rhsrep
      egraph := { egraph with rep2users := egraph.rep2users.erase rhsrep }
      egraph :=
        let lhsUsers := egraph.rep2users.find! lhsrep;
        { egraph with rep2users := egraph.rep2users.insert lhsrep (lhsUsers ++ rhsUsers) }
      -- TODO: should this be done first?
      for userPtr in rhsUsers do
        trace[EggTactic.egg] "{← getIndent2}userPtr:{userPtr}"
        let user ← egraphDeref userPtr
        trace[EggTactic.egg] "{← getIndent2}user:{user}"
        let user' := user.replaceAllUsesWith (old := rhs) (new := lhs)
        -- user' should be canonical, because we got it by derefing a pointer,
        -- and then replacing 'rhs' with 'lhs' (also a canonical pointer.)
        -- let user' ← canonicalizeHashCons user'
        match egraph.canon2ptr.find? user' with
        | .none =>
          let _ ← egraphAddHashCons user'
        | .some user'Ptr =>
          let proof := EqProof.replace
            (oldExpr := ← Ptr.toExpr rhs)
            (newExpr := ← Ptr.toExpr lhs)
            (prf := rhs2lhs)
          egraphEnqueueUnite userPtr user'Ptr proof
      -- 4. canon2ptr : HashMap ExprHashCons Ptr
      egraph := { egraph with canon2ptr := egraph.canon2ptr.erase (← egraphDeref rhsrep)}
      return egraph

end -- UNITE

-- saturate the Egraph with respect to an equality, and return
-- an explanation of why 'lhs' = 'rhs' if possible
def egraphAddEq (lhs rhs : Expr) (prf : EqProof) : EggM Unit := do
  let lhsptr ←
    match ← egraphAddExpr lhs with
    | .none => return ()
    | .some p => pure p
  let rhsptr ←
    match ← egraphAddExpr rhs with
    | .none => return ()
    | .some p => pure p
  egraphEnqueueUnite  lhsptr rhsptr prf
  egraphPropagate

-- Return a proof that 'lhsPtr' = 'rhsPtr', if they are in the same
-- e-class.
def egraphGetEqProof (lhsPtr rhsPtr : Ptr) : EggM (Option EqProof) := withIndent do
  trace[EggTactic.egg] f!"{←getIndent}getEq {lhsPtr} =?= {rhsPtr}=>"
  let (lhsPtrRep, lhs2lhsrep) ← ptr2repWithProof lhsPtr
  let (rhsPtrRep, rhs2rhsrep) ← ptr2repWithProof rhsPtr
  trace[EggTactic.egg] f!"{←getIndent2}lhs:{lhsPtr} → rep:{lhsPtrRep}"
  trace[EggTactic.egg] f!"{←getIndent2} prf: '{lhs2lhsrep}'"
  trace[EggTactic.egg] f!"{←getIndent2}rhs:{rhsPtr} → rep:{rhsPtrRep}"
  trace[EggTactic.egg] f!"{←getIndent2} prf: '{rhs2rhsrep}'"
  if lhsPtrRep == rhsPtrRep
  then
    trace[EggTactic.egg] f!"{←getIndent2}getEq {lhsPtrRep} == {rhsPtrRep}"
    let out := .sequence lhs2lhsrep rhs2rhsrep.sym
    trace[EggTactic.egg] f!"{←getIndent2}<= out"
    return .some <| out
  else
    trace[EggTactic.egg] f!"{←getIndent2}getEq {lhsPtrRep} ≠ {rhsPtrRep}"
    trace[EggTactic.egg] f!"{←getIndent2}<= .none"
    return .none


open Lean Meta Elab Tactic in
def runProof : EqProof → EggM Unit
| .rfl => withIndent do
  trace[EggTactic.egg] f!"{←getIndent}run rfl"
  (← getMainGoal).refl
| .leanProof prf => withIndent do
    trace[EggTactic.egg] f!"{←getIndent}run leanProof {prf}"
    match ← isDefEq (Expr.mvar (← getMainGoal)) prf with
    | true => pure ()
    | false => throwError "unable to run Lean proof 'prf'."; return ()
| .sym_ prf => withIndent do
  trace[EggTactic.egg] f!"{←getIndent}run sym {prf}"
  let freshMVar ← mkFreshExprMVar (← getMainTarget)
  match ← isDefEq (Expr.mvar (← getMainGoal)) (← mkEqSymm freshMVar) with
  | true => pure ()
  | false => throwError "unable to run symmetry before '{prf}'"; return ()
  replaceMainGoal [freshMVar.mvarId!]
  runProof prf
| .sequence_ prf1 prf2 => withIndent do
  runProof prf1
  runProof prf2
| .replace oldExpr newExpr prf => do
  -- first create an mvar of type (old = new) and use that to rewrite the rest.
  -- then prove (old = new) by using rewrite via 'prf'.
  let eqType ← mkEq oldExpr newExpr
  let replaceMVar ← mkFreshExprMVar eqType
    -- note that we use `rewrite` instead of the more targeted
    -- `isDefEq` because we might use a proof multiple times (?)
    -- for e.g., when we call `replace`? NOTE: think if this is actually true
  let rewriteResult ← (← getMainGoal).rewrite (← getMainTarget) replaceMVar
  match rewriteResult.mvarIds with
  | [] => pure ()
  | _ =>
    throwError "expected zero goals, but instead found {rewriteResult.mvarIds} as goals"
  replaceMainGoal [replaceMVar.mvarId!]
  runProof prf


declare_syntax_cat eggconfigval
declare_syntax_cat eggconfig

syntax "(" "timeLimit" ":=" num ")" : eggconfigval
syntax "noInstantiation" : eggconfigval
syntax "dump" : eggconfigval
syntax "oneSided" : eggconfigval
syntax "simplify" : eggconfigval
syntax eggconfigval eggconfig : eggconfig
syntax eggconfigval : eggconfig

def runEggM (em : EggM α) : TacticM α :=  do
  let (a, _) ← em.run default
  return a

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
/-
  -- let mvarId' ← (← getMainGoal).replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
  -- replaceMainGoal (mvarId' :: rewriteResult.mvarIds)
  -- let goal'ty <- inferType (Expr.mvar goal')
  -- trace[EggTactic.egg] (s!"18) new goal: {goal'.name} : {goal'ty}")
  -- replaceMainGoal [goal'] -- replace main goal with new goal + subgoals
-/

elab "eggxplosion" "[" rewriteNames:ident,* "]" c:(eggconfig)? : tactic => withMainContext do
  runEggM do
  let _rewriteNames : HashSet Name :=
    HashSet.insertMany ∅ <| rewriteNames.getElems.map Syntax.getId
  trace[EggTactic.egg] s!"{←getIndent}goal '{← getMainTarget}'"
  let (_, goalLhs, goalRhs) ←
    match (← matchEq? (← getMainTarget)) with
    | .none => throwError "Egg: target not equality: {← getMainTarget}"
    | .some eq => pure eq
  let _cfg : EggConfig := match c with
    | none => default
    | some cfgSyn => cfgSyn.getEggConfig
  for hyp in (← getMainDecl).lctx do
    if hyp.isImplementationDetail then continue
    -- if not (rewriteNames.contains hyp.userName) then continue
    let (_, hypLhs, hypRhs) ←
      match (← matchEq? hyp.type) with
      | .none =>
        trace[EggTactic.egg] s!"skip hyp {hyp.userName} : {hyp.type}"
        continue
      | .some data => pure data
    trace[EggTactic.egg] s!"+hyp {hyp.userName} : {hyp.type}"
    egraphAddEq hypLhs hypRhs (EqProof.leanProof <| Expr.fvar hyp.fvarId)
  let goalLhsPtr ←
    match ← egraphAddExpr goalLhs with
    | .some ptr => pure ptr
    | .none => do
      throwError s!"unable to add goal LHS '{goalLhs}"
      return ()

  let goalRhsPtr ←
    match ← egraphAddExpr goalRhs with
    | .some ptr => pure ptr
    | .none => do
      throwError s!"unable to add goal RHS '{goalRhs}'"
      return ()

  match ← egraphGetEqProof goalLhsPtr goalRhsPtr with
  | .some prf =>
      trace[EggTactic.egg] "found equality proof '{prf}'"
      -- runProof prf
      return ()
  | .none =>
      trace[EggTactic.egg] s!"goal LHS '{goalLhsPtr}' /= RHS '{goalRhsPtr}'"
      return ()
