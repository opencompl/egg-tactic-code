import EggTactic
import EggTactic.ExtractLean
namespace Test


inductive List α
  | nil : List α
  | cons : α → List α → List α


notation a "::"  b => List.cons a b
notation "[" "]" => List.nil

-- From init/data/list/basic.lean

def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

/- I should be able to derive these directly in the tactic... -/
def append_nil : ∀ (bs:  List α), append ([] : List α) bs = bs := by
  intros
  rfl

def append_cons : ∀ (a : α) (as bs : List α), append (a :: as) bs = a :: (append as bs) := by
  intros
  rfl

instance {α : Type _} : HAppend (List α) (List α) (List α) where hAppend := append

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil =>
    extract Test.append_nil -- propositional equality
    eggxplosion [append_nil, append_cons]
  | cons a as ih => eggxplosion [ih, append_nil, append_cons] -- could this also be automated?
  -- <;> eggxplosion


def reverseAux : List α → List α → List α
  | [],   r => r
  | a::l, r => reverseAux l (a::r)

def List.reverse (as : List α) :List α :=
  reverseAux as []

def reverseAux_nil : ∀ r : List α, reverseAux ([] : List α) r = r := by
  intros
  rfl

def reverseAux_cons : ∀ (l r : List α) (a : α) , reverseAux (a :: l) r = reverseAux l (a :: r) := by
  intros
  rfl

def reverse_def : ∀ l : List α, l.reverse = reverseAux l [] := by
  intros
  rfl

theorem reverseAux_eq_append (as bs : List α) : reverseAux as bs = reverseAux as [] ++ bs := by
  induction as generalizing bs with
  | nil => eggxplosion [reverseAux_nil, reverseAux_cons]
  | cons a as ih =>
    eggxplosion [reverseAux_nil, reverseAux_cons, append_assoc]
  -- <;> eggxplosion [reverseAux, append_assoc]

theorem reverse_cons (a : α) (as : List α) : List.reverse (a :: as) = List.reverse as ++ (a :: List.nil) := by
  eggxplosion [reverse_def, reverseAux_nil, reverseAux_cons, reverseAux_eq_append]

theorem reverse_append (as bs : List α) : (as ++ bs).reverse = bs.reverse ++ as.reverse := by
  induction as generalizing bs with
  | nil => eggxplosion []
  | cons a as ih => eggxplosion [ih, append_assoc]
  -- <;> eggxplosion [append_assoc]

def List.map : (α → β) → List α  → List β
  | _, [] => []
  | f, (a :: as) => (f a) :: (as.map f)

def List.foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | a :: l => f a (foldr f init l)

-- A short cut to deforestation, Gill, Launchbury, Peyton Jones
def all (p : α → Bool) (xs : List α) : Bool := (List.map p xs).foldr and true

def all' : (α → Bool) → List α → Bool
  | _, [] => true
  | p, (x::xs) => (p x) && (all' p xs)

theorem all_deforestation {α} : ∀ (p : α → Bool) (xs : List α), all p xs = all' p xs := by
  -- eggxplosion [all, all', map, foldr]
  intros p xs
  try induction xs with
    | nil => simp [all, all', List.foldr, List.map]
    | cons a as ih => simp [all, all', List.foldr, List.map, ih]
  eggxplosion [all, all', List.foldr, List.map] -- add induction explicitly (like in Agda?)
