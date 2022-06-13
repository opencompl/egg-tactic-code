import EggTactic
namespace Egg

-- From: lean4/tests/lean/run/alg.lean

-- class Group (α : Type u) extends Mul α where
--   one : α
--   one_mul (a : α) : one * a = a
--   mul_one (a : α) : a * one = a
--   inv : α → α
--   mul_assoc (a b c : α) : a * b * c = a * (b * c)
--   mul_left_inv (a : α) : (inv a) * a = one
--
-- instance [Group α] : OfNat α (nat_lit 1) where
-- ofNat := Group.one

-- Does not work with typeclasses (problem with metavariables)

-- We'll just take the integers for now and not use any additional properties
-- Copied form stdlib
inductive G : Type where
| ofNat   : Nat → G
| negSucc : Nat → G

def negOfNat : Nat → G
| 0       => .ofNat 0
| .succ m => .negSucc m

def neg (n : G) : G :=
match n with
 | .ofNat n   => negOfNat n
 | .negSucc n => .ofNat $ Nat.succ n

def subNatNat (m n : Nat) : G :=
 match (n - m : Nat) with
 | 0        => G.ofNat (m - n)  -- m ≥ n
 | (.succ k) => .negSucc k

def add (m n : G) : G :=
match m, n with
  | .ofNat m,   .ofNat n   => .ofNat (m + n)
  | .ofNat m,   .negSucc n => subNatNat m (Nat.succ n)
  | .negSucc m, .ofNat n   => subNatNat n (Nat.succ m)
  | .negSucc m, .negSucc n => .negSucc (Nat.succ (m + n))

postfix:max "⁻¹" => neg
infix:80 "∘" => add
notation "e" => G.ofNat 0

theorem one_mul (a : G) : e ∘ a = a := by sorry
theorem mul_assoc (a b c : G) : (a ∘ b) ∘ c = a ∘ (b ∘ c) := by sorry
theorem mul_one (a : G) : a ∘ e = a := by sorry
theorem mul_left_inv (a : G) : a⁻¹ ∘ a = e by sorry
theorem mul_right_inv (a : G) : a ∘ a⁻¹  = e by sorry

theorem inv_mul_cancel_left (a b : G) : a⁻¹ ∘ (a ∘ b) = b := by
  try simp [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]
  rawEgg [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]

theorem mul_inv_cancel_left : a ∘ (a⁻¹ ∘ b) = b := by
 try simp [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]
 rawEgg [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]

theorem inv_mul : (a ∘ b)⁻¹ = b⁻¹ ∘ a⁻¹ := by
 try simp [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]
 rawEgg [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]

theorem one_inv : e⁻¹ = e := by
 try simp [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]
 rawEgg [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]

theorem inv_inv : a ⁻¹ ⁻¹ = a := by
  try simp [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]
  rawEgg [mul_assoc,mul_left_inv,mul_assoc,one_mul,mul_one, mul_right_inv]

