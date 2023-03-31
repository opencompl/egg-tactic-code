import Std.Data.HashMap
open Std HashMap 

namespace Egraph 

structure Ptr (α : Type) where
  ix : UInt64

-- typeclass that can dereference points of type 'α'
class DerefM (m : Type → Type) (α : Type) where
  deref : Ptr α -> m (Option α)
  set : Ptr α -> α -> m Unit
  new : α → m (Ptr α) -- allocate new memory.

abbrev Memory (α : Type) := HashMap UInt64 α

notation "*" x => DerefM.deref x -- dereference a pointer
notation p " ^= " v => DerefM.set p v -- set a pointer to a value

-- terms.
structure HashConsTerm where

-- equivalence class of terms.
structure Eclass where

-- the data of the Egraph state.
structure State where 
  eclasses : Memory Eclass
  hashconsterms : Memory HashConsTerm

abbrev M α := StateM State α

-- deref an e-class
instance : DerefM M Eclass where 
  deref ptr := do 
    return (← get).eclasses.find? ptr.ix
  set ptr v := modify (fun s => 
    { s with eclasses := s.eclasses.insert ptr.ix v : State })
  new v := do
    let ix := UInt64.ofNat (← get).eclasses.size
    let ptr := Ptr.mk ix
    modify (fun s => 
      { s with eclasses := s.eclasses.insert ptr.ix v : State })
    return ptr

instance : DerefM M HashConsTerm where 
  deref ptr := do 
    return (← get).hashconsterms.find? ptr.ix
  set ptr v := modify (fun s => 
    { s with hashconsterms := s.hashconsterms.insert ptr.ix v : State })
  new v := do
    let ix := UInt64.ofNat (← get).hashconsterms.size
    let ptr := Ptr.mk ix
    modify (fun s => 
      { s with hashconsterms := s.hashconsterms.insert ptr.ix v : State })
    return ptr


-- substitutions for patterns to create terms.
-- abbrev PatternS