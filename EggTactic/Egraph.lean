import Std.Data.HashMap
open Std HashMap 

namespace Egraph 

-- We key pointers with names instead of types so that
-- we can have names of structures that does not create a cycle.
-- When defining a structure, we are not allowed to use the
-- type of the structure in the body of the structure.
-- We dodge this restriction by converting to names.
-- Convention: all pointer variables will have name starting
-- with π. e.g. πx is a pointer to x.
structure Ptr (_α : Name) where ix : UInt64
deriving DecidableEq, Hashable,Inhabited 

-- typeclass that can dereference points of type 'o' named by 'α'
class DerefM (m : Type → Type) (α : Name) (o : outParam Type) where
  deref : Ptr α -> m (Option o)
  set : Ptr α -> o -> m Unit
  malloc  [Inhabited o] : m (Ptr α) -- allocate junk memory

def DerefM.new [Monad m] [DerefM m α o] [Inhabited o] (v : o) : m (Ptr α) := do 
  let ptr ← malloc
  set ptr v 
  return ptr

-- dereference pointer and run action. action must succeed.
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
-- notation "^" x => Ptr `x

-- terms.
structure HashConsTerm (σ : Type) where
  head : σ
  args : Array (Ptr `Egraph.Eclass) 
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

-- create a singleton e class.
def Eclass.singleton (πcanon : Ptr ``Eclass) (member : HashConsTerm σ) : Eclass σ where 
  members := #[member]
  parentTerms := {}
  πcanon := πcanon
  subtreeSize := 0

-- add a term and the e-class that owns the term as the parent
-- of this e-class.
-- we add the parent e-class as well as the term since this informatoin
-- is useful when moving terms around during the update.
def Eclass.addParent (cls : Eclass σ) 
  (tm : HashConsTerm σ)
  (πtm_cls : Ptr ``Eclass) := 
  { cls with parentTerms := cls.parentTerms.push (tm, πtm_cls) } 

-- the data of the Egraph state.
structure State (σ : Type)  where
  σinhabited : Inhabited σ
  σbeq : DecidableEq σ 
  σhashable : Hashable σ
  eclasses : Memory (Eclass σ)
  hashconsterms : Memory (HashConsTerm σ)
  term2classp : HashMap (HashConsTerm σ) (Ptr ``Eclass)

def State.new [Inhabited σ] [DecidableEq σ] [Hashable σ] : State σ where 
  σinhabited := inferInstance
  σbeq := inferInstance
  σhashable := inferInstance
  eclasses := {}
  hashconsterms := {}
  term2classp := {}

abbrev M σ α := StateM (State σ) α

-- deref an e-class
instance : DerefM (M σ) ``Eclass (Eclass σ) where 
  deref ptr := do 
    return (← get).eclasses.find? ptr.ix
  set ptr v := modify (fun s => 
    { s with eclasses := s.eclasses.insert ptr.ix v : State σ })
  malloc := do 
    let ptr := Ptr.mk <| UInt64.ofNat (← get).eclasses.size
    return ptr 

instance : DerefM (M σ) ``HashConsTerm (HashConsTerm σ) where 
  deref ptr := do 
    return (← get).hashconsterms.find? ptr.ix
  set ptr v := modify (fun s => 
    { s with hashconsterms := s.hashconsterms.insert ptr.ix v : State σ })
  malloc := do 
    let ptr := Ptr.mk <| UInt64.ofNat (← get).eclasses.size
    return ptr 

class Canonicalize (σ : Type) (α : Type) where 
  canonicalize : α → M σ α

-- return canonical pointer
notation "⟦" x "⟧" => Canonicalize.canonicalize x 

partial def canonicalizeClass (πcls :  Ptr ``Eclass) : M σ (Ptr ``Eclass) := do 
    let cls : (Eclass σ) ← πcls.deref!
    if cls.πcanon == πcls
    then return πcls
    else do 
      let πcanon ← Egraph.canonicalizeClass πcls
      πcls ^= { cls with πcanon := πcanon }
      return πcanon

instance : Canonicalize σ (Ptr ``Eclass) where 
  canonicalize := canonicalizeClass

 partial def canonicalizeHashConsTerm (htm : HashConsTerm σ) : 
  M σ (HashConsTerm σ) := do
  let _ : Inhabited σ := (← get).σinhabited
  let htm := { htm with args := (← htm.args.mapM canonicalizeClass) } 
  return htm

instance : Canonicalize σ (HashConsTerm σ) where
  canonicalize := canonicalizeHashConsTerm

partial def HashConsTerm.find! (htm : HashConsTerm σ) :
  M σ (Ptr ``Eclass) := do 
  match (← get).term2classp.find? (← ⟦htm⟧) with 
  | .some cls => return cls
  | .none => panic! "unable to find e-class"
  
partial def HashConsTerm.findOrAdd (htm : HashConsTerm σ) :
  M σ (Ptr ``Eclass) := do 
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

mutual 

-- rebuild E-graph
partial def Egraph.unite (πc πd : Ptr ``Eclass) : M σ (Ptr ``Eclass) := do 
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

-- rebuild E-class.
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
