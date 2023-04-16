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
deriving DecidableEq, Hashable,Inhabited

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
def Ptr.deref! [Inhabited o] [Monad m] [DerefM m α o] (p : Ptr α) : m o:=
  Option.get! <$> DerefM.deref p

abbrev Memory (α : Type) := HashMap UInt64 α
notation "*?" x => DerefM.deref x -- dereference a pointer
set_option quotPrecheck false in
notation "*" x => (← Ptr.deref! x) -- dereference a pointer
notation p " ^= " v => DerefM.set p v -- set a pointer to a value

/-- terms. -/
structure HashConsTerm (σ : Type) where
  head : σ
  args : Array (Ptr `Egraph.Eclass) := #[]
deriving BEq, DecidableEq, Hashable, Inhabited

-- equivalence class of terms.
structure Eclass (σ : Type) where
  members : Array (HashConsTerm σ)
  -- TODO: cannot use (Ptr Eclass) here :(
  -- lmao, just use names!
  parentTerms : Array (HashConsTerm σ × Ptr `Egraph.Eclass)
  πcanon : Ptr `Egraph.Eclass -- pointer to canonical eclass represenative
  subtreeSize : UInt64 -- union find subtree size
deriving BEq, DecidableEq, Hashable, Inhabited

/-- create a singleton e class. -/
def Eclass.singleton (πcanon : Ptr ``Eclass) (member : HashConsTerm σ) : Eclass σ where
  members := #[member]
  parentTerms := {}
  πcanon := πcanon
  subtreeSize := 0

/-- add a term and the e-class that owns the term as the parent
of this e-class.
we add the parent e-class as well as the term since this informatoin
is useful when moving terms around during the update. --/
def Eclass.addParent (cls : Eclass σ)
  (tm : HashConsTerm σ)
  (πtm_cls : Ptr ``Eclass) :=
  { cls with parentTerms := cls.parentTerms.push (tm, πtm_cls) }


abbrev Error : Type := String

/-- the data of the Egraph state. -/
structure State (σ : Type)  where
  σinhabited : Inhabited σ
  σbeq : DecidableEq σ
  σhashable : Hashable σ
  eclasses : Memory (Eclass σ)
  hashconsterms : Memory (HashConsTerm σ)
  term2classp : HashMap (HashConsTerm σ) (Ptr ``Eclass)
  errors : Array Error

def State.new [Inhabited σ] [DecidableEq σ] [Hashable σ] : State σ where
  σinhabited := inferInstance
  σbeq := inferInstance
  σhashable := inferInstance
  eclasses := {}
  hashconsterms := {}
  term2classp := {}
  errors := #[]


/-- TODO: add error -/
abbrev T (σ : Type) (m : Type → Type) (α : Type) : Type := StateT (State σ) m α
abbrev M σ α := T σ Id α

def logError [Monad m] : Error → T σ m Unit
| e => modify fun s => { s with errors := s.errors.push e }

/-- deref an e-class -/
instance [Monad m] : DerefM (T σ m) ``Eclass (Eclass σ) where
  deref ptr := do
    return (← get).eclasses.find? ptr.ix
  set ptr v := modify (fun s =>
    { s with eclasses := s.eclasses.insert ptr.ix v : State σ })
  malloc := do
    let ptr := Ptr.mk <| UInt64.ofNat (← get).eclasses.size
    return ptr

instance [Monad m] : DerefM (T σ m) ``HashConsTerm (HashConsTerm σ) where
  deref ptr := do
    return (← get).hashconsterms.find? ptr.ix
  set ptr v := modify (fun s =>
    { s with hashconsterms := s.hashconsterms.insert ptr.ix v : State σ })
  malloc := do
    let ptr := Ptr.mk <| UInt64.ofNat (← get).eclasses.size
    return ptr

class Canonicalize (σ : Type) (α : Type) where
  canonicalize [Monad m] : α → T σ m α

/-- return canonical pointer -/
notation "⟦" x "⟧" => Canonicalize.canonicalize x

partial def canonicalizeClass [Monad m]
  (πcls :  Ptr ``Eclass) : T σ m (Ptr ``Eclass) := do
    let cls : (Eclass σ) ← πcls.deref!
    if cls.πcanon == πcls
    then return πcls
    else do
      let πcanon ← Egraph.canonicalizeClass πcls
      πcls ^= { cls with πcanon := πcanon }
      return πcanon

instance : Canonicalize σ (Ptr ``Eclass) where
  canonicalize := canonicalizeClass

 partial def canonicalizeHashConsTerm [Monad m] (htm : HashConsTerm σ) :
  T σ m (HashConsTerm σ) := do
  let _ : Inhabited σ := (← get).σinhabited
  let htm := { htm with args := (← htm.args.mapM canonicalizeClass) }
  return htm

instance : Canonicalize σ (HashConsTerm σ) where
  canonicalize := canonicalizeHashConsTerm

/-- Find e-class of the given E graph. -/
partial def HashConsTerm.find! [Monad m] (htm : HashConsTerm σ) :
  T σ m (Ptr ``Eclass) := do
  match (← get).term2classp.find? (← ⟦htm⟧) with
  | .some cls => return cls
  | .none => panic! "unable to find e-class"


partial def HashConsTerm.findOrAdd [Monad m] (htm : HashConsTerm σ) :
  T σ m (Ptr ``Eclass) := do
  let htm ← ⟦htm⟧
  let πhtm_cls ←
    match (← get).term2classp.find?  htm with
    | .some x => pure x
    | .none => do
        let πhtm_cls ← DerefM.malloc (α := ``Eclass)
        modify (fun state => { state with term2classp := state.term2classp.insert htm πhtm_cls })
        πhtm_cls ^= Eclass.singleton (πcanon := πhtm_cls) (member := htm)
        return πhtm_cls
  -- for each argument, update the parent e-elcass by adding a pointer to the
  -- e class of htm
  for πarg in htm.args do
    πarg.modify! (fun cls => cls.addParent htm πhtm_cls)
  return πhtm_cls


abbrev HashConsTerm.add [Monad m] (htm : HashConsTerm σ) : T σ m (Ptr ``Eclass) :=
   htm.findOrAdd
mutual

/-- unite E classes in a E graph -/
partial def Egraph.unite (πc πd : Ptr ``Eclass) :
  M σ (Ptr ``Eclass) := do
  let πc ← ⟦ πc ⟧
  let πd ← ⟦ πd ⟧
  if πc == πd then return πc
  -- attach root of lighter thing to root of heavier thing, so that there is
  -- a chance that depth does not go up.
  let (πparent, πchild) :=
    if (← πc.deref!).subtreeSize >= (← πd.deref!).subtreeSize
    then (πc, πd)
    else (πd, πc)

  πchild.modify! (fun c => { c with πcanon :=  πparent })
  πparent.modifyM! (fun c => do return {
    c with subtreeSize := c.subtreeSize + (← πchild.deref!).subtreeSize
  })
  πparent.modifyM! (fun c => do return {
    c with
    members := c.members ++ (← πchild.deref!).members,
    parentTerms := c.parentTerms ++ (← πchild.deref!).parentTerms
  })
  πchild.modify! (fun c => { c with members := #[], parentTerms := #[] })
  Egraph.rebuild πparent
  return πparent

/-- rebuild E-class. -/
partial def Egraph.rebuild (πc : Ptr ``Eclass) : M σ Unit := do
  let mut parents := #[]
  for (htm, πhtm_old_cls) in (← πc.deref!).parentTerms do
    let πhtm_new_cls ← htm.findOrAdd
    let πhtm_new_cls ← Egraph.unite πhtm_old_cls πhtm_new_cls
    modify (fun s => { s with term2classp := (s.term2classp.erase htm)} )
    let htm ← ⟦ htm ⟧
    modify (fun s => { s with term2classp := s.term2classp.insert htm πhtm_new_cls } )
    parents := parents.push (htm, πhtm_new_cls)
  πc.modify! (fun c => { c with parentTerms := parents})

end

abbrev PatVarIx := UInt64
abbrev Subst σ := HashMap PatVarIx (HashConsTerm σ)

/-- empty substitution -/
def Subst.empty : Subst σ := HashMap.empty

-- E matching patterns
inductive Pattern (σ : Type)
| var (ix : PatVarIx)
| term (head : σ) (args : Array (Pattern σ))

-- try to instantiate the pattern given a substitution.
partial def Pattern.instantiate? (s: Subst σ): Pattern σ → M σ (Option (HashConsTerm σ))
| .var ix => return s.find? ix
| .term head pargs => do
   let mut args : Array (Ptr ``Eclass) := #[]
   for arg in pargs do
    match (← arg.instantiate? s) with
    | .none => return .none
    | .some tm => args := args.push (← tm.find!)
   return HashConsTerm.mk head args

partial def Pattern.matcher [DecidableEq σ] [Monad m]
  [DerefM m ``Egraph.Eclass (Egraph.Eclass σ)]
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
        let cls : Eclass σ ← πargcls.deref!
        for cls_htm in cls.members do
          substs ← substs.concatMapM (parg.matcher cls_htm)
      return substs
    else return #[]

structure Equivalence (σ : Type) where
  lhs : Pattern σ
  rhs : Pattern σ


inductive Progress where
| MadeProgress
| NoProgress

-- TODO: add explanation generation.
inductive Explanation (σ : Type)
| reflexivity
-- TODO: cache equivalences by name / pointer
| rewrite (eqv : Equivalence σ) (subst : Subst σ)
-- transitivity of rewrites
| transitivity (middle : HashConsTerm σ)

/-- Return whether the pattern successfully rewrote on the Egraph,
  and the matching substitution if it did. -/
partial def Equivalence.run (e: Equivalence σ)
 [DecidableEq σ] : M σ Progress := do
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
       let _cls ← Egraph.unite  (← htm.find!) (← htm'.find!)
   return progress
