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

-- | unrolled version of Expr with internal nodes
-- replaced with α
inductive ExprF (α : Type) where
| const (declName : Name) (us : List Level)
| fvar (fvarId : FVarId)
| app (f : α) (arg : α)
| lit (lit : Literal)
deriving BEq, Hashable, Inhabited


-- | TODO: write a fusion law so we don't traverse structure twice?
def ExprF.toExpr : ExprF Expr → Expr
| .const declName us => .const declName us
| .app f arg => .app f arg
| .lit l => .lit l
| .fvar fvarId => .fvar fvarId


def ExprF.mapFoldlM {m : Type → Type} {β σ : Type} [Monad m] (act : σ → α → m (β × σ)) (init : σ)  : ExprF α → m (ExprF β × σ)
| .const declName us => return (.const declName us, init)
| .fvar fvarId => return (.fvar fvarId, init)
| .app ef earg => do
  let (ef', init) ← act init ef
  let (earg', init) ← act init earg
  return (.app ef' earg', init)
| .lit l => return (.lit l, init)

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

def ExprF.accumMGo [Monad m] (act : α → m β) (arr : Array β) : ExprF α → m (Array β)
| .const _ _ => pure arr
| .fvar _ => pure arr
| .app f arg => do
  let arr := arr.push (← act f)
  let arr := arr.push (← act arg)
  return arr
| .lit _ => pure arr

def ExprF.accumM [Monad m] (act : α → m β) (e : ExprF α) : m (Array β) :=
   e.accumMGo act #[]

def ExprF.foldlM [Monad m] (act : σ → α → m σ) (state : σ) : ExprF α → m σ
| .const _ _ => pure state
| .fvar _ => pure state
| .app f arg => do
  let state ← act state f
  let state ← act state arg
  return state
| .lit _ => pure state

abbrev ExprHashCons := ExprF Ptr


inductive EqProof where
| leanProof (oldExpr : Expr) (prf : Expr) (newExpr : Expr)
| rfl (obj : Expr)
| sym_ (prf : EqProof)
| sequence_ (prf1 prf2 : EqProof)
| exprF (prf: ExprF EqProof)
deriving BEq, Hashable

def parenIf : Bool → MessageData → MessageData
| true, f => f.paren
| false, f => f

mutual
partial def EqProof.oldExpr : EqProof → Expr
| .leanProof oldExpr _e _newExpr => oldExpr
| .rfl obj => obj
| .sym_ prf => EqProof.newExpr prf
| .sequence_ prf1 _prf2 => EqProof.oldExpr prf1
| .exprF prf => (prf.map EqProof.oldExpr).toExpr


partial def EqProof.newExpr : EqProof → Expr
| .leanProof _oldExpr _e newExpr => newExpr
| .rfl obj => obj
| .sym_ prf => EqProof.oldExpr prf
| .sequence_ _prf1 prf2 => EqProof.newExpr prf2
| .exprF prf => (prf.map EqProof.newExpr).toExpr
end


instance : Inhabited EqProof where
  default := EqProof.leanProof (Expr.lit <| .strVal "DEFAULT") default default

/- smart constructor for sequencing proofs -/
def EqProof.sequence : EqProof → EqProof → EqProof
| .rfl _, x => x
| x, .rfl _ => x
| x, y => .sequence_ x y

/-- smart constructor for taking symmetric version of proof --/
def EqProof.sym : EqProof → EqProof
| .rfl x => .rfl x
| .sym_ (sequence_ (sym_ x) (sym_ y)) => sequence y x
| .sym_ (sequence_ x y) => sequence y.sym x.sym
| .sym_ x => x
| x => .sym_ x


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
def getIndent4 : EggM Indent := do return (← get).indent.increment.increment
def withIndent (m : EggM α) : EggM α := fun s => do
  let indent := s.indent
  let (a, s) ← m { s with indent := indent.increment }
  let s := { s with indent := indent }
  return (a, s)

class ToMessageDataM (α : Type) where
  toMessageDataM : α → EggM MessageData
open ToMessageDataM

instance  [ToMessageDataM α] [ToMessageDataM β] : ToMessageDataM (α × β) where
  toMessageDataM := fun (a, b) => do
    return m!"({← toMessageDataM a}, {← toMessageDataM b})"

def ExprF.toMessageDataM (fmt : α → EggM MessageData) : ExprF α → EggM MessageData
| .const declName us => return m!"const:{declName} {us}"
| .fvar fvarId => return m!"fvar:{← fvarId.getUserName}"
| .app f arg => do return m!"({← fmt f} {← fmt arg})"
| .lit l => do return m!"lit:{repr l}"

instance [ToMessageDataM α] : ToMessageDataM (ExprF α) where
  toMessageDataM := ExprF.toMessageDataM toMessageDataM

instance [ToMessageData α] : ToMessageDataM α where -- low priority
  toMessageDataM := pure ∘ toMessageData

partial def EqProof.toMessageDataM : (precedence : Nat := 0) → EqProof → EggM MessageData
  | _, .leanProof _old prf _new => return m!"𝕷{toMessageData prf}"
  | _i, .rfl _obj => return "rfl"
  | _i, .sym_ p => return m!"sym {← p.toMessageDataM 100}"
  | i, .sequence_ p1 p2 => return parenIf (i > 0) m!"{← p1.toMessageDataM}; {← p2.toMessageDataM}"
  | _i, .exprF prf => return m!"𝔉{← prf.toMessageDataM (EqProof.toMessageDataM)}"

-- sym a ; b -> sym (a ; b) ?
instance : ToMessageDataM EqProof where
  toMessageDataM e := e.toMessageDataM

/-- abbreviation for toMessageDataM -/
abbrev msgM [ToMessageDataM α] : α → EggM MessageData := toMessageDataM

partial def Ptr.canonicalizeWithProof (p : Ptr) : EggM (RepPtr × EqProof) := withIndent do
  let egraph := (← get).egraph
  let (parent, p2parent) := egraph.ptr2ptr.find! p
  trace[EggTactic.egg] "{← getIndent}Ptr.canonicalize p:{p}=>"
  if parent == p then
    trace[EggTactic.egg] "{←getIndent2}<=parent:{parent} prf:{← msgM p2parent}"
    return (p, p2parent)
  else
    let (rep, parent2rep) ← Ptr.canonicalizeWithProof parent
    let prf := EqProof.sequence p2parent parent2rep
    let egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert p (rep, prf) }
    trace[EggTactic.egg] "{←getIndent2}<=parent:{parent} prf:{← msgM prf}"
    modifyGet fun s => ((rep, prf), { s with egraph := egraph })

def Ptr.deref (p : Ptr) : EggM ExprHashCons :=  do
  return (← get).egraph.rep2canon.find! p

def RepPtr.deref (p : RepPtr) : EggM ExprHashCons := Ptr.deref p


mutual -- TOEXPR
partial def ExprHashCons.toExpr (eh : ExprHashCons) : EggM Expr := do
  return ExprF.toExpr (← eh.mapM Ptr.toExpr)

partial def Ptr.toExpr (ptr : Ptr) : EggM Expr := do
  ExprHashCons.toExpr (← Ptr.deref ptr)
end -- TOEXPR


/- an ExprHashCons annotate with proofs that tell us how to get to the canonicalized ptr in question -/
abbrev ExprPrfHashCons := ExprF (RepPtr × EqProof)

def ExprHashCons.canonicalize (ehc : ExprHashCons) : EggM ExprPrfHashCons := withIndent do
  trace[EggTactic.egg] "{←getIndent}canonicalize {← msgM ehc}=>"
  let out ← ehc.mapM (fun p => do
    let e  : Expr ← (← p.deref).toExpr
    let (pcanon, eqproof) ← Ptr.canonicalizeWithProof p
    let ecanon : Expr ← (← pcanon.deref).toExpr
    -- return (pcanon, EqProof.replace e eqproof ecanon))
    return (pcanon, eqproof))
  trace[EggTactic.egg] "{←getIndent2}<={← msgM out}"
  return out


/-- replace all uses of old with new, and produce a proof witnessing equality.
  TODO: this can be made much faster by only producing the proof when necessary
  TODO: Also notice that `replaceAllUsesWith` is _just_ canonicalize before we know that
  `old → new`.
  Returns if the value was changed, and an annotated proof
-/
def ExprHashCons.replaceAllUsesWith (old new : Ptr) (old2new : EqProof) (ehc : ExprHashCons) : EggM (Bool × ExprPrfHashCons) := do
  trace[EggTactic.egg] "{←getIndent}rauw {old} {new} {← msgM old2new} {← msgM ehc}=>"
  let (out, changed?) ← ehc.mapFoldlM (σ := Bool) (init := False) <| fun changed? p => do
    let e  : Expr ← (← p.deref).toExpr
    if p == old then
      return ((old, EqProof.rfl e), changed?) -- pointer unchanged.
    else
      return ((new, old2new), True) -- pointer changed
  trace[EggTactic.egg] "{←getIndent2}<={← msgM out}"
  return (changed?, out)


def egraphAppendUser (userPtr : Ptr) (usedPtr : RepPtr)
  (g : Egraph) : EggM Egraph := withIndent do
  trace[EggTactic.egg] "{←getIndent}appendUser {userPtr} uses {usedPtr}=>"
  let users := g.rep2users.find! usedPtr
  return { g with rep2users := g.rep2users.insert usedPtr (users.push userPtr) }

-- Optimisation
mutual
partial def EqProof.isRfl : EqProof → Bool
| _ => false
-- | .rfl _ => true
-- | .replace _ prf _ => prf.isRfl
-- | .exprF prf => prf.isRfl
-- | _ => false

partial def ExprF.isRfl (e : ExprF EqProof) : Bool :=
  Id.run <| e.foldlM (m := Id) (state := True) (fun b prf => b && prf.isRfl)
end

mutual -- UNITE

partial def ExprPrfHashCons.add (canonAndProof : ExprPrfHashCons) : EggM Ptr := withIndent do
  let canon := canonAndProof.map Prod.fst
  let prf := canonAndProof.map Prod.snd
  let ptr ← modifyGetEgraphM fun egraph => do
    let mut egraph := egraph
    match egraph.canon2ptr.find? canon with
    | .none =>
        trace[EggTactic.egg] "{←getIndent2}egraph[canon] → .none" -- TODO: add 'Indent'
        let canonPtr : Ptr := egraph.ptrGensym
        egraph := { egraph with ptrGensym := egraph.ptrGensym + 1 }
        trace[EggTactic.egg] "{←getIndent2}egraph[canon] ← {canonPtr}" -- TODO: add 'Indent'
        -- 1. update `rep2canon`
        egraph := { egraph with rep2canon := egraph.rep2canon.insert canonPtr canon }
        -- 2. update `rep2users`.
        for used in  (← canon.accumM pure) do
          egraph ← egraphAppendUser (userPtr := canonPtr) (usedPtr := used) egraph
        -- 3. update `ptr2ptr`
        let obj ← ExprHashCons.toExpr canon
        egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert canonPtr (canonPtr, .rfl obj) }
        -- 4. update `canon2ptr`
        egraph := { egraph with canon2ptr := egraph.canon2ptr.insert canon canonPtr }
        return (canonPtr, egraph)
    | .some canonPtr =>
        -- | if the proof that goes from canonical to our pointer is rfl, then we can
        -- safely reuse the pointer.
        if prf.isRfl then return (canonPtr, egraph)
        else
          trace[EggTactic.egg] "{←getIndent2}egraph[canon] → .some '{canonPtr}'"
          let newPtr : Ptr := egraph.ptrGensym
          egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert newPtr (canonPtr,  EqProof.exprF prf) }
          trace[EggTactic.egg] "{←getIndent2}<='gensymd pointer {newPtr}'"
          return (newPtr, egraph)
  return ptr
  -- egraphEnqueueUnite userPtr userPtr' (userRAUW.proofF)

-- TODO: think if this really should canonicalize?
-- TODO: see if we can extract this out.
partial def ExprHashCons.canonicalizeAndAdd (ehc : ExprHashCons) : EggM Ptr := withIndent do
  trace[EggTactic.egg] "{←getIndent}+hashcons 'ehc:{← msgM ehc}'=>" -- TODO: add 'Indent'
  let canonAndProof ← ExprHashCons.canonicalize ehc
  ExprPrfHashCons.add canonAndProof

-- | Calling unite will only enque a unite. must call propagate()
partial def egraphEnqueueUnite (lhs rhs : Ptr) (lhs2rhs : EqProof) : EggM Unit :=
  withIndent do
    trace[EggTactic.egg] "{← getIndent}∪ lhs:{lhs} rhs:{rhs}=>"
    trace[EggTactic.egg] "{← getIndent2}lhs2rhs:{← msgM lhs2rhs}"
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
      trace[EggTactic.egg] "{← getIndent}lhs2rhs:{← msgM lhs2rhs}=>"
      let mut egraph := egraph
      -- 5. pending : List (Ptr × Ptr × EqProof) -- pending updates.
      egraph := { egraph with pending := pending } -- pop
      let (lhsrep, lhs2lhsrep) ← Ptr.canonicalizeWithProof lhs
      let (rhsrep, rhs2rhsrep) ← Ptr.canonicalizeWithProof rhs
      let rhsrep2rhs := rhs2rhsrep.sym
      let rhs2lhs := lhs2rhs.sym
      let rhsrep2lhsrep :=
         (rhsrep2rhs.sequence rhs2lhs).sequence lhs2lhsrep
      -- merge rhs into lhs.
      -- 3. ptr2ptr : HashMap Ptr (Ptr × EqProof)
      trace[EggTactic.egg] "{← getIndent2}uniting rhs:{rhsrep} into lhsrep:{lhsrep}"
      trace[EggTactic.egg] "{← getIndent2}propagate prf: {← msgM rhsrep2lhsrep}"
      egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert rhsrep (lhsrep, rhsrep2lhsrep) }
      -- 1. rep2canon : HashMap RepPtr ExprHashCons -- must be represenattive pointer.
      -- store the canonical element of rhs so we can remap rhscanon to lhsrep
      egraph := { egraph with rep2canon := egraph.rep2canon.erase rhsrep }
      -- 2. rep2users : HashMap RepPtr (Array Ptr) -- must be representative pointer.
      let rhsUsers := egraph.rep2users.find! rhsrep
      egraph := { egraph with rep2users := egraph.rep2users.erase rhsrep }
      egraph :=
        let lhsUsers := egraph.rep2users.find! lhsrep;
        { egraph with rep2users := egraph.rep2users.insert lhsrep (lhsUsers ++ rhsUsers) }
      -- TODO: should this be done first?
      -- | After we setup the ptr → ptr, we re-add every user into the egraph.
      -- this assumes that we canonicalize.
      for userPtr in rhsUsers do
        let user ← userPtr.deref
        let (changed?, userRAUW) ← user.replaceAllUsesWith (old := rhs) (new := lhs) (old2new := rhs2lhs)
        let canon := userRAUW.map Prod.fst
        let canonProof := EqProof.exprF <| userRAUW.map Prod.snd
        if not changed?
        then pure () -- do nothing
        else do -- stuff changed, so add a new value and ask for unification.
          -- TODO: check if we can have code reuse with `ExprPrfHashcons.add`
          match egraph.canon2ptr.find? (userRAUW.map Prod.fst) with
          | .none => -- there's no one else like us, there's nothing to propagate. We add our pointer and move on.
            trace[EggTactic.egg] "{←getIndent2}egraph[canon] → .none" -- TODO: add 'Indent'
            let canonPtr : Ptr := egraph.ptrGensym
            egraph := { egraph with ptrGensym := egraph.ptrGensym + 1 }
            trace[EggTactic.egg] "{←getIndent2}egraph[canon] ← {canonPtr}" -- TODO: add 'Indent'
            -- 1. update `rep2canon`
            egraph := { egraph with rep2canon := egraph.rep2canon.insert canonPtr canon }
            -- 2. update `rep2users`.
            for used in  (← canon.accumM pure) do
              egraph ← egraphAppendUser (userPtr := canonPtr) (usedPtr := used) egraph
            -- 3. update `ptr2ptr`
            let obj ← ExprHashCons.toExpr canon
            egraph := { egraph with ptr2ptr := egraph.ptr2ptr.insert canonPtr (canonPtr, .rfl obj) }
            -- 4. update `canon2ptr`
            egraph := { egraph with canon2ptr := egraph.canon2ptr.insert canon canonPtr }
          | .some canonPtr => -- there is someone else like us, we need to propagate a unification request with them.
            -- trace[EggTactic.egg] "{← getIndent}∪ lhs:{lhs} rhs:{rhs}=>"
            -- trace[EggTactic.egg] "{← getIndent2}lhs2rhs:{← msgM lhs2rhs}"
            egraph := { egraph with pending := (userPtr, canonPtr, canonProof) :: egraph.pending }
      return egraph

end -- UNITE

-- Return a proof that 'lhsPtr' = 'rhsPtr', if they are in the same
-- e-class.
def egraphGetEqProof (lhsPtr rhsPtr : Ptr) : EggM (Option EqProof) := withIndent do
  trace[EggTactic.egg] m!"{←getIndent}getEq {lhsPtr} =?= {rhsPtr}=>"
  let (lhsPtrRep, lhs2lhsrep) ← Ptr.canonicalizeWithProof lhsPtr
  let (rhsPtrRep, rhs2rhsrep) ← Ptr.canonicalizeWithProof rhsPtr
  trace[EggTactic.egg] m!"{←getIndent2}lhs:{lhsPtr} → rep:{lhsPtrRep}"
  trace[EggTactic.egg] m!"{←getIndent2} prf: '{← msgM lhs2lhsrep}'"
  trace[EggTactic.egg] m!"{←getIndent2}rhs:{rhsPtr} → rep:{rhsPtrRep}"
  trace[EggTactic.egg] m!"{←getIndent2} prf: '{← msgM rhs2rhsrep}'"
  if lhsPtrRep == rhsPtrRep
  then
    trace[EggTactic.egg] m!"{←getIndent2}getEq {lhsPtrRep} == {rhsPtrRep}"
    let out := .sequence lhs2lhsrep rhs2rhsrep.sym
    trace[EggTactic.egg] m!"{←getIndent2}<= out"
    return .some <| out
  else
    trace[EggTactic.egg] m!"{←getIndent2}getEq {lhsPtrRep} ≠ {rhsPtrRep}"
    trace[EggTactic.egg] m!"{←getIndent2}<= .none"
    return .none

#check MVarId.rewrite

/-- finish the main goal. If no proof, then use reflexivity -/
def runFinisher (prf? : Option Expr) : EggM Unit := withIndent do
  trace[EggTactic.egg] m!"{←getIndent}runFinisher=>"
  trace[EggTactic.egg] m!"{←getIndent2}prf: {prf?}"
  trace[EggTactic.egg] m!"{←getIndent2}main goal type: {← getMainTarget}"
  trace[EggTactic.egg.debug] m!"{←getIndent2}main goal: {← getMainGoal}"
  if (← getGoals).isEmpty then
    trace[EggTactic.egg] m!"{←getIndent2}main goal empty."
    throwError "{←getIndent2}main goal empty."
  else
    match prf? with
    | .some prf =>
      trace[EggTactic.egg] m!"{←getIndent2}prf type: {← inferType prf}"
      match ← isDefEq (← getMainTarget) (← inferType prf) with
      | true =>
        withMainContext (closeMainGoal prf)
        trace[EggTactic.egg] m!"{← getIndent2}<= defEq ∎"
      | false =>
        trace[EggTactic.egg] m!"{← getIndent2}<=ERROR: failed to unify '{← getMainTarget}' with '{← inferType prf}'"
        throwError "{← getIndent2}<=ERROR: failed to unify '{← getMainTarget}' with '{← inferType prf}'"
    | .none =>
      (← getMainGoal).refl
      trace[EggTactic.egg] m!"{← getIndent2}<= refl ∎"


#check Lean.MVarId.rewrite
def rewriteAt (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (occs : Occurrences := Occurrences.all) (config := { : Rewrite.Config }) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let cont (heq heqType : Expr) : MetaM RewriteResult := do
      match (← matchEq? heqType) with
      | none => throwTacticEx `rewrite mvarId m!"equality or iff proof expected{indentExpr heqType}"
      | some (α, lhs, rhs) =>
        let cont (heq heqType lhs rhs : Expr) : MetaM RewriteResult := do
          if lhs.getAppFn.isMVar then
            throwTacticEx `rewrite mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
          let e ← instantiateMVars e
          let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs occs
          unless eAbst.hasLooseBVars do
            throwTacticEx `rewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}"
          -- construct rewrite proof
          let eNew := eAbst.instantiate1 rhs
          let eNew ← instantiateMVars eNew
          let eEqE ← mkEq e e
          let eEqEAbst := mkApp eEqE.appFn! eAbst
          let motive := Lean.mkLambda `_a BinderInfo.default α eEqEAbst
          unless (← isTypeCorrect motive) do
            throwTacticEx `rewrite mvarId "motive is not type correct"
          let eqRefl ← mkEqRefl e
          let eqPrf ← mkEqNDRec motive eqRefl heq
          postprocessAppMVars `rewrite mvarId newMVars binderInfos
          let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
          let otherMVarIds ← getMVarsNoDelayed eqPrf
          let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
          let newMVarIds := newMVarIds ++ otherMVarIds
          pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
        match symm with
        | false => cont heq heqType lhs rhs
        | true  => do
          let heq ← mkEqSymm heq
          let heqType ← mkEq rhs lhs
          cont heq heqType rhs lhs
    match heqType.iff? with
    | some (lhs, rhs) =>
      let heqType ← mkEq lhs rhs
      let heq := mkApp3 (mkConst `propext) lhs rhs heq
      cont heq heqType
    | none =>
      cont heq heqType


open Lean Meta Elab Tactic in
partial def mkProof (prf : EqProof) : EggM Expr := withIndent do
  trace[EggTactic.egg] m!"{←getIndent}mkProof '{← msgM prf}'=>"
  trace[EggTactic.egg] m!"{←getIndent2}⊢ {prf.oldExpr} = {prf.newExpr}"
  let goalTy ← mkEq prf.oldExpr prf.newExpr
  match prf with
  | .rfl x =>
      mkEqRefl prf.oldExpr
  | .sym_ p =>
     mkEqSymm (← mkProof p)
  | .leanProof old prf new =>
    return prf
  | .sequence_ prf1 prf2 => withIndent do
    mkEqTrans (← mkProof prf1) (← mkProof prf2)
  | .exprF prfF =>
    trace[EggTactic.egg] m!"do not know how to run exprF: {← msgM prfF}"
    throwError m!"do not know how to run exprF: {← msgM prfF}"



-- NOTE: testUnassigned
-- ====================
-- We allow unassigned variables because we use metavars to create 'holes' in the proof.
open Lean Meta Elab Tactic in
partial def runProof (prf : EqProof) :  EggM Unit := withIndent do
  trace[EggTactic.egg] m!"{←getIndent}runProof '{← msgM prf}'=>"
  trace[EggTactic.egg] m!"{←getIndent2}⊢ {← getMainTarget}"
  trace[EggTactic.egg.debug] m!"{←getIndent2}goal:"
  trace[EggTactic.egg.debug] m!"{←getIndent2}{← getMainGoal}"
  let (lhsrhsType, hypLhs, hypRhs) ←
    match (← matchEq? (← getMainTarget)) with
    | .none =>
      trace[EggTactic.egg] m!"{←getIndent2}<= ERROR: goal is not equalty"
      throwError "goal state is not equality"
    | .some data => pure data
  match prf with
  | .rfl x => withIndent do
     runFinisher .none
  | .leanProof old prf new => withIndent do
     runFinisher prf
  | .sym_ prf => withIndent do
    let symType ← mkEq hypRhs hypLhs
    let symProof ← mkFreshExprMVar (type? := symType)

    let mainGoal ← getMainGoal
    setGoals [symProof.mvarId!]
    runProof prf

    setGoals [mainGoal]
    runFinisher (← mkEqSymm symProof)
  | .sequence_ prf1 prf2 => withIndent do

    let mainGoal ← getMainGoal
    -- TODO: I need to create a metavar for the intermediate type
    let midTy ← mkFreshExprMVar (type? := lhsrhsType)
    let goalLhsMid ← mkFreshExprMVar (type? := ← mkEq hypLhs midTy)
    let goalMidRhs ← mkFreshExprMVar (type? := ← mkEq midTy hypRhs)

    -- do not use `setMainGoal`, as that assumes we have something called as a main goal.
    setGoals [goalLhsMid.mvarId!]
    runProof prf1

    setGoals [goalMidRhs.mvarId!]
    runProof prf2

    setGoals [mainGoal]
    let mainPrf ← mkEqTrans goalLhsMid goalMidRhs
    runFinisher mainPrf
  | .exprF exprFPrf => do
    trace[EggTactic.egg] m!"{←getIndent2}--exprF {← msgM exprFPrf}--"
    let mainGoal ← exprFPrf.foldlM (σ := MVarId) (state := ← getMainGoal) fun mainGoal p => do
      -- prove the rewrite
      trace[EggTactic.egg] m!"{←getIndent2}subterm equality: {p.oldExpr} ={← msgM p}= {p.newExpr}"
      let pMvar ← mkFreshExprMVar (type? := ← mkEq p.oldExpr p.newExpr)
      setGoals [pMvar.mvarId!]
      runProof p
      -- runFinisher .none -- do I need this?
      trace[EggTactic.egg] m!"{←getIndent2}closed subgoal ∎"

      -- rewrite subterm in main goal
      trace[EggTactic.egg] m!"{←getIndent2}rewriting {← msgM p} in main goal ⊢{← mainGoal.getType}"
      setGoals [mainGoal]
      let rewriteResult ← (← getMainGoal).rewrite (← getMainTarget) pMvar
      match rewriteResult.mvarIds with
      | [newMainGoal] => do
        trace[EggTactic.egg] m!"{←getIndent2}new main goal ⊢{← newMainGoal.getType}"
        pure newMainGoal
      | errGoals =>
          trace[EggTactic.egg] m!"{←getIndent2}ERROR: expected exactly 1 goal, but found {errGoals.length} goals"
          for goal in errGoals do
            trace[EggTactic.egg] m!"{←getIndent2}ERROR: ⊢{goal}"
          throwError "expected exactly one goal, but instead found {errGoals} as goals"
    -- main term should be 'rfl'.
    setGoals [mainGoal]
    trace[EggTactic.egg] m!"{←getIndent2}proving final goal ⊢{← mainGoal.getType}"
    runFinisher .none


open Lean Elab Meta Tactic in
mutual
partial def egraphAddExpr (e : Expr) : EggM (Option Ptr) := withIndent do
  trace[EggTactic.egg] "{←getIndent}+expr {e}=>"
  let out ← egraphAddExprGo e
  trace[EggTactic.egg] "{←getIndent2}<={out}"
  return out
partial def egraphAddExprGo : Expr → EggM (Option Ptr)
| .const declName ls =>
  ExprHashCons.canonicalizeAndAdd <| ExprF.const declName ls
| .fvar id =>
  ExprHashCons.canonicalizeAndAdd <| ExprF.fvar id
| .app f arg => do
  let fh ←
    match ← egraphAddExpr f with
    | .some f => pure f
    | .none => return .none
  let argh ←
    match ← egraphAddExpr arg with
    | .some arg => pure arg
    | .none => return .none
  ExprHashCons.canonicalizeAndAdd <| .app fh argh
| .lit name =>
  ExprHashCons.canonicalizeAndAdd <| .lit name
| _ => return .none
end

-- saturate the Egraph with respect to an equality, and return
-- an explanation of why 'lhs' = 'rhs' if possible
def egraphAddEq  (prf : EqProof) : EggM Unit := withIndent do
  trace[EggTactic.egg] m!"+eq {prf.oldExpr} {← msgM prf} {prf.newExpr}"
  let lhsptr ←
    match ← egraphAddExpr prf.oldExpr with
    | .none => return ()
    | .some p => pure p
  let rhsptr ←
    match ← egraphAddExpr prf.newExpr with
    | .none => return ()
    | .some p => pure p
  egraphEnqueueUnite  lhsptr rhsptr prf
  egraphPropagate


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
  trace[EggTactic.egg] m!"{←getIndent}goal '{← getMainTarget}'"
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
        trace[EggTactic.egg] m!"skip hyp {hyp.userName} : {hyp.type}"
        continue
      | .some data => pure data
    trace[EggTactic.egg] m!"+hyp {hyp.userName} : {hyp.type}"
    egraphAddEq (EqProof.leanProof hypLhs (Expr.fvar hyp.fvarId) hypRhs)
  let goalLhsPtr ←
    match ← egraphAddExpr goalLhs with
    | .some ptr => pure ptr
    | .none => do
      throwError m!"unable to add goal LHS '{goalLhs}"
      return ()

  let goalRhsPtr ←
    match ← egraphAddExpr goalRhs with
    | .some ptr => pure ptr
    | .none => do
      throwError m!"unable to add goal RHS '{goalRhs}'"
      return ()

  match ← egraphGetEqProof goalLhsPtr goalRhsPtr with
  | .some prf =>
      trace[EggTactic.egg] "found equality proof '{← msgM prf}' for '{← getMainTarget}'"
      runProof prf
      trace[EggTactic.egg] "finished running proof ∎"
  | .none =>
      trace[EggTactic.egg] m!"goal LHS '{goalLhsPtr}' /= RHS '{goalRhsPtr}'"
      return ()
