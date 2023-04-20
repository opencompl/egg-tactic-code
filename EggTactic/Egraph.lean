import Std.Data.HashMap
open Std HashMap

namespace Egraph

/-- We key pointers with names instead of types so that
we can have names of structures that does not create a cycle.
When defining a structure, we are not allowed to use the
type of the structure in the body of the structure.
We dodge this restriction by converting to names.
Convention: all pointer variables will have name starting
with π. e.g. πx is a pointer to x. -/
structure Ptr (_α : Name) where ix : UInt64
deriving DecidableEq, BEq, Hashable,Inhabited

class StoreM (m : Type → Type) (α : Type)  where
  storeGet : m (Array α)
  storeAppend : α → m (Array α)

/-- typeclass that can dereference points of type 'o' named by 'α' -/
class DerefM (m : Type → Type) (α : Name) (o : outParam Type) where
  deref : Ptr α -> m (Option o)
  set : Ptr α -> o -> m Unit
  malloc  [Inhabited o] : m (Ptr α) -- allocate junk memory

def DerefM.new [Monad m] [DerefM m α o] [Inhabited o] (v : o) : m (Ptr α) := do
  let ptr ← malloc
  set ptr v
  return ptr

/-- dereference pointer and run action. action must succeed. -/
def Ptr.modifyM! [Monad m] [DerefM m α o] [Inhabited o]
  (f : o → m o) (p : Ptr α) : m Unit := do
  let v ← Option.get! <$> (DerefM.deref p)
  DerefM.set p (← f v)

def Ptr.modify! [Monad m] [DerefM m α o] [Inhabited o]
  (f : o → o) (p : Ptr α) : m Unit :=
  p.modifyM! (fun o => pure (f o))

def Ptr.deref [DerefM m α o] (p : Ptr α) : m (Option o) := DerefM.deref p
def Ptr.derefM! [Inhabited o] [Monad m] [DerefM m α o] (p : Ptr α) : m o:=
  Option.get! <$> DerefM.deref p

abbrev Memory (α : Type) := HashMap UInt64 α
notation "*?" x => DerefM.deref x -- dereference a pointer
set_option quotPrecheck false in
notation "*"x => Ptr.derefM! x -- dereference a pointer
notation p " ^= " v => DerefM.set p v -- set a pointer to a value

/-- terms. -/
structure HashConsTerm (σ : Type) where
  head : σ
  args : Array (Ptr `Egraph.Eclass) := #[]
deriving BEq, Hashable, Inhabited -- TODO: check that we don't use DecidableEq

/-- Typeclass that ρ is the type of equalities over α -/
class Reason (ρ : outParam Type) (α : Type) extends Inhabited ρ where
  refl : HashConsTerm α → ρ
  -- concatenate proofs. (a = b); (b = c)
  sequence : ρ → ρ → ρ
  sym : ρ → ρ
  -- given reasons for subterms being equivalent, create reason for term.
  -- [eq] → new
  subterm : Array ρ → ρ
  rewrite : HashConsTerm σ → ρ → ρ

instance [R : Reason ρ σ] : Inhabited ρ where
  default := R.default



/-- equivalence class of terms. Eclass <kind> <reason for union> -/
-- Need to have pointers for proofs as well
-- Really need something like `ekmett/structs`.
structure Eclass (σ : Type) (ρ : Type) [BEq σ] [Hashable σ]  where
  -- map each term in the e-class to its proof that it is iso to the canonical representative.
  memberProofs : HashMap (HashConsTerm σ) ρ
  users : Array (HashConsTerm σ) -- terms that use this Eclass.
  termcanon : HashConsTerm σ -- canonical representative of this eclass.
deriving Inhabited

/-- create a singleton e class. -/
def Eclass.singleton [R : Reason ρ σ] [Hashable σ] [BEq σ]
  (member : HashConsTerm σ) : Eclass σ ρ where
  memberProofs := HashMap.ofList [(member, R.refl member)]
  users := {}
  termcanon := member

/-- add a term and the e-class that owns the term as the parent
of this e-class.
we add the parent e-class as well as the term since this informatoin
is useful when moving terms around during the update. --/
def Eclass.addUser [BEq σ] [Hashable σ] (cls : Eclass σ ρ)
  (tm : HashConsTerm σ) : Eclass σ ρ :=
  { cls with users := cls.users.push tm }


abbrev Error : Type := String

@[reducible]
class Symbol (σ : Type) extends Hashable σ, BEq σ, Inhabited σ where

instance [Hashable σ] [BEq σ] [Inhabited σ] : Symbol σ where

/-- the data of the Egraph state. -/
structure State (σ : Type) (ρ : Type) [S : Symbol σ] [R : Reason ρ σ] where
  eclasses : Memory (Eclass σ ρ)
  hashconsterms : Memory (HashConsTerm σ)
  term2classp : HashMap (HashConsTerm σ) (Ptr ``Eclass)
  pending : List (Ptr ``Eclass × Ptr ``Eclass × ρ)
  errors : Array Error

def State.new [Symbol σ] [Reason ρ σ] : State σ ρ where
  eclasses := {}
  hashconsterms := {}
  term2classp := {}
  pending := []
  errors := #[]


/-- TODO: add error -/
abbrev T (σ ρ : Type) (m : Type → Type) [S : Symbol σ] [R : Reason ρ σ] (α : Type)  : Type :=
  StateT (State σ ρ) m α

abbrev M (σ ρ : Type) [Symbol σ] [Reason ρ σ] (α : Type)  : Type :=
  StateT (State σ ρ) Id α

def logError [Monad m] [Symbol σ] [Reason ρ σ] : Error → T σ ρ m Unit
| e => modify fun s => { s with errors := s.errors.push e }

/-- deref an e-class -/
instance [Monad m] [Symbol σ] [Reason ρ σ] : DerefM (T σ ρ m) ``Eclass (Eclass σ ρ) where
  deref ptr := do
    return (← get).eclasses.find? ptr.ix
  set ptr v := modify (fun s =>
    { s with eclasses := s.eclasses.insert ptr.ix v : State σ ρ })
  malloc := do
    let ptr := Ptr.mk <| UInt64.ofNat (← get).eclasses.size
    return ptr

instance [Monad m] [Symbol σ] [Reason ρ σ] : DerefM (T σ ρ m) ``HashConsTerm (HashConsTerm σ) where
  deref ptr := do
    return (← get).hashconsterms.find? ptr.ix
  set ptr v := modify (fun s =>
    { s with hashconsterms := s.hashconsterms.insert ptr.ix v : State σ ρ})
  malloc := do
    let ptr := Ptr.mk <| UInt64.ofNat (← get).eclasses.size
    return ptr


partial def HashConsTerm.findOrAdd [Symbol σ] [R : Reason ρ σ]
  [Monad m] (htm : HashConsTerm σ) :
  T σ ρ m (Ptr ``Eclass) := do
    match (← get).term2classp.find? htm with
    | .some x => pure x
    | .none => do
        let πhtm_cls ← DerefM.malloc (α := ``Eclass)
        modify fun state => { state with term2classp := state.term2classp.insert htm πhtm_cls }
        πhtm_cls ^= Eclass.singleton htm
        return πhtm_cls


def Egraph.addPending (πc πd: Ptr ``Eclass) (uniteReason : ρ) [Symbol σ] [Reason ρ σ] : M σ ρ Unit :=
  modify fun s => { s with pending := (πc, πd, uniteReason) :: s.pending }

def Egraph.popPending [Symbol σ] [Reason ρ σ]: M σ ρ (Option (Ptr ``Eclass × Ptr ``Eclass × ρ)) :=
  modifyGet fun s =>
    match s.pending with
    | [] => (.none, { s with pending := [] })
    | x :: xs => (x, { s with pending := xs })


/-- proof that this term is equiv to the represenrtative of its eclass -/
def HashConsTerm.eclassProof [Symbol σ] [Reason ρ σ] (t : HashConsTerm σ) : M σ ρ ρ := do
  let cls : Eclass σ ρ ← (← t.findOrAdd).derefM!
  return cls.memberProofs.find! t


def HashConsTerm.modifyWithEclassProof [Symbol σ] [Reason ρ σ] (t : HashConsTerm σ)
  (f: ρ → ρ) : M σ ρ Unit := do
  let πcls ← t.findOrAdd
  let cls : Eclass σ ρ ← πcls.derefM!
  let prf' := f (cls.memberProofs.find! t)
  πcls.modify! fun cls => { cls with memberProofs := cls.memberProofs.insert t prf' }

-- return prf of t --> t'
def HashConsTerm.replaceAllUsesWith [Symbol σ] [R : Reason ρ σ] (t : HashConsTerm σ)
  (old new : Ptr ``Egraph.Eclass) (reason : ρ) : M σ ρ (HashConsTerm σ × ρ) := do
    -- TODO: this is interesting, the direction matters a lot.
    -- t' ---(sym ρargs)--> t --t.eclassProof--> tcanon=[old]---old2new--> [new]
    let mut args := #[]
    let mut ρs := #[]
    for arg in t.args do
      if arg == old then
        args := args.push new
        ρs := ρs.push reason
      else
        args := args.push old
        ρs := ρs.push reason
    let prf := (R.sequence (R.sym (R.subterm ρs)) (← t.eclassProof))
    let trm := { t with args := args }
    return (trm, prf)

mutual

/-- unite E classes in a E graph. `uniteReason` should say how to get from
 e-class representative of (πc) to (πd) -/
partial def Egraph.unite [Symbol σ] [R : Reason ρ σ]
  (πc πd : Ptr ``Eclass) (uniteReason : ρ) :
  M σ ρ Unit := do
  Egraph.addPending πc πd uniteReason
  Egraph.propagate



partial def Egraph.propagate [Symbol σ] [R : Reason ρ σ]
  : M σ ρ Unit := do
  match (← Egraph.popPending) with
  | .none => return ()
  | .some (πc, πd, reason) =>
        let (πc, πd) :=
          if (← πc.derefM!).memberProofs.size <= (← πd.derefM!).memberProofs.size
          then (πc, πd)
          else (πd, πc)
        -- TODO: think about this carefully tomorrow.
        -- -- We can either first perform the union and then update our users,
        -- -- or first update our users and then perform the union.
        -- let mut members : HashMap (HashConsTerm σ) ρ := HashMap.empty
        -- for (mem, prf) in (← πc.derefM!).users.toList do
        --   let (mem', prfmem2mem') ← user.replaceAllUsesWith πc πd reason
        --   let πcls' ← mem'.findOrAdd
        --   let mem'2canon ← mem'.eclassProof

        --
        --
        -- -- Since we have not performed the union, replacing πc with πd will
        -- -- give us the canonical representation.
        -- -- We walk all our users [who may be our members!] and we
        -- -- add the unions they may induce into the log.
        -- for user in (← πc.derefM!).users.toList do
        --   let (user', ρuser2user') ← user.replaceAllUsesWith πc πd reason
        --   match (← get).term2classp.find? user' with
        --   | .none => users' := sorry
        --   | .some πcls' =>
        --       let reason := R.sequence prf term'2term
        --       Egraph.addPending πc πcls' reason
        -- return sorry
        -- match (← get).term2classp.find? user with
        -- | .none => continue
        -- | .some cls' => Egraph.addPending cls cls'


end


/--
TODO: add API on top of the core Egraph to re-canonicalize Eclass pointers.
This will allow users to keep 'stale' pointers that are laundered.
The core Egraph API always assumes that the pointers are fresh.
-/

abbrev PatVarIx := UInt64
abbrev Subst σ := HashMap PatVarIx (Egraph.HashConsTerm σ)

/-- empty substitution -/
def Subst.empty : Subst σ := HashMap.empty

-- E matching patterns
inductive Pattern (σ : Type)
| var (ix : PatVarIx)
| term (head : σ) (args : Array (Pattern σ))

-- try to instantiate the pattern given a substitution.
partial def Pattern.instantiate? (s: Subst σ) [Symbol σ] [Reason ρ σ] : Pattern σ →
  M σ ρ (Option (HashConsTerm σ))
| .var ix => return s.find? ix
| .term head pargs => do
   let mut args : Array (Ptr ``Eclass) := #[]
   for arg in pargs do
    match (← arg.instantiate? s) with
    | .none => return .none
    | .some tm => args := args.push (← tm.find!).fst
   return HashConsTerm.mk head args

partial def Pattern.matcher [Symbol σ] [Reason ρ σ] [DerefM m ``Egraph.Eclass (Egraph.Eclass σ ρ)]
  (pat : Pattern σ)
  (htm : HashConsTerm σ) (s : Subst σ) : m (Array (Subst σ)) := do
  match pat with
  | .var ix =>
    match s.find? ix with
    | .none => return #[s.insert ix htm]
    | .some htm' => if htm = htm' then return #[s] else return #[]
  | .term head pargs =>
    if head = htm.head
    then do
      let mut substs : Array (Subst σ) := #[s]
      if pargs.size != htm.args.size then return #[]
      for (πargcls, parg) in htm.args.zip pargs do
        let cls : Eclass σ ρ ← πargcls.derefM!
        for cls_htm in cls.members do
          substs ← substs.concatMapM (parg.matcher cls_htm)
      return substs
    else return #[]

structure Equivalence (σ : Type) where
  lhs : Pattern σ
  rhs : Pattern σ



/-- Non-boolean blind inductive to represent progress -/
inductive Progress
| NoProgress
| MadeProgress

/-- Return whether the pattern successfully rewrote on the Egraph,
  and the matching substitution if it did. -/
partial def Equivalence.run (e: Equivalence σ) [Reason ρ σ]
 [BEq σ] [Inhabited σ] [Inhabited ρ] : M σ ρ Progress := do
   let mut progress := Progress.NoProgress
   for (_k, htm) in (← get).hashconsterms.toArray do
     let substs ← e.lhs.matcher htm Subst.empty
     for subst in substs do
       progress := Progress.MadeProgress
       let htm'? ← e.rhs.instantiate? subst
       -- | Do we know which substitutions will yield the same E-class?
       -- We want to enumerate (E/subst)/cls instead of (E/cls)/subst.
       -- ^ The above feels like a non-trivial insight, if there is an
       -- algorithm for it.
       let htm' ← match htm'? with
         | .some v => pure v
         | .none =>
             logError s!"RHS has more free vars than LHS"
             return progress
       let _ ← Egraph.unite  (← htm.find!).fst (← htm'.find!).fst reason
   return progress
