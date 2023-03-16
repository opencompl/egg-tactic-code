import EggTactic
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Real.Basic
import Mathbin.Data.Polynomial.Basic
import Mathbin.RingTheory.PowerSeries.Basic
-- import Mathlib.Data.Polynomial.Taylor -- Taylor expansions but just for polynomials

-- From generatingfuctionology 1.1:
--
/-
    x / ((1 - x) (1 - 2*x))
  = x * ( (2 / 1 - 2*x) - (1 / 1 - x) )
  = (2*x + 2^2*x^2 + 2^3*x^3 + 2^4*x^4 + ...) - (x + x^2 + x^3 + x^4 + ...)
  = (2 - 1)*x + (2^2 - 1)*x^2 + (2^3 - 1)*x^3 + (2^4 - 1)*x^4 + ...-/
-/

noncomputable def rhs := @PowerSeries.mk Real (fun n => (2^n - 1)) -- (2 - 1)*x + (2^2 - 1)*x^2 + (2^3 - 1)*x^3 + (2^4 - 1)*x^4 + ...-
noncomputable def denominator := (@PowerSeries.mk Real (fun n => if n = 0 then 1 else (if n = 1 then -1 else 0))) * (@PowerSeries.mk Real (fun n => if n = 0 then 1 else (if n = 1 then -2 else 0)))
noncomputable def lhs := (@PowerSeries.mk Real (fun n => if n = 1 then 1 else 0)) * PowerSeries.inv (denominator)

theorem lhs_eq_rhs : lhs = rhs := by
    simp [lhs, rhs, denominator]
    sorry

-- Power series in Mathlib seem to be pretty ugly though...
--
-- From: Francesco Lacava, "Classical Electrodynamics", 2.3 Multipole Expansion for the Potential of a Distribution of Point Charges
--
-- dᵢ and r are the vector positions of the charge qᵢ and point P, respectively, and rᵢ is the vector from the ith charge to P. Then:
-- notation "ℝ" => Real
abbrev R3 := Real -- Module Real (Fin 3 → Real)
variable (di r : R3)
noncomputable def ri : R3 := r - di

-- 1/rᵢ = 1/|r - dᵢ| =  1/((r - dᵢ)*(r - dᵢ))^(1/2) = 1/(r² - 2 r * dᵢ + dᵢ²)^(1/2) = 1/r * 1/(1 + (dᵢ² - 2 r ⬝ dᵢ) / r²)^(1/2)
--
theorem first_reduction : 1/ri = (1/r) * 1/(1 + ((di^2 - (2 * r) * di) / r^2))^(1/2) := by sorry

-- If we define α = (dᵢ² - 2 r ⬝ dᵢ) / r², since r >> dᵢ, α is a very small fraction and the last equation can be expanded in a power series:
noncomputable def α :=  (di^2 - 2 * r * di) / r^2

-- Taylor expansion
theorem alpha_approximation : 1/(1 + α)^(1/2) = 1 - 1/2 * α + 3/8 * α² - 15/48 * α³ ...

--
--
--  1/(1 + α)^(1/2) = 1 - 1/2 * α + 3/8 * α² - 15/48 * α³ ...
--
-- And keeping terms only to second order in α:
-- 1/rᵢ = 1/r * (1 - 1/2 * (dᵢ² - 2 * r ⬝ dᵢ) / r² + 3/8 * (dᵢ² - 2 * r ⬝ dᵢ)² / r⁴)
--
-- and neglecting terms with higher power than dᵢ/r squared we get:
--
-- 1/rᵢ = 1/r + (dᵢ * r̂)/ r² + 1/r³ * ( 3/2 * (dᵢ²* r̂)² - 1/2 * dᵢ²)
--



-- An example of a fuzzy issue ()
--
--
theorem some_identity_linarith (x y: Nat): (x + y) * (x + y) = x * x + 2 * x * y + y * y :=
  by linarith

--set_option trace.EggTactic.egg true in
--theorem some_identity (x y: Nat): (x + y) * (x + y) = x * x + 2 * x * y + y * y :=
--  by eggxplosion [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.mul_comm, Nat.one_mul, Nat.mul_one, Nat.mul_zero]

theorem some_identity_calc (x y: Nat): (x + y) * (x + y) = x * x + 2 * x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]
    _ = x * x + x * y + x * y + y * y              := by simp [Nat.mul_comm]
    _ = x * x + 2 * x * y + y * y  := by sorry

    -- rw [←Nat.two_mul] -- ???
/-
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/hello/near/340556180
Kevin Buzzard: Parcly Taxel said:

how do I get the rewrite to work on the last line here?

example (x y: Nat): (x + y) * (x + y) = x * x + 2 * x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              := by rw [←Nat.add_assoc]
    _ = x * x + x * y + x * y + y * y              := by simp [Nat.mul_comm]
    _ = x * x + 2 * x * y + y * y  := by rw [←Nat.two_mul] -- ???

The issue is that x * x + x * y + x * y + y * y is actually ((x * x + x * y) + x * y) + y * y so x * y + x * y is not actually a subterm. You'll have to do a targetted rewrite of add_assoc to make this approach work. This is exactly why ring exists, to save us from having to go through this sort of stuff (sure it's fun to start with, but the novelty wears off after a while when you start actually making a gigantic mathematical library).

-/

-- From "Deep Learning", Chapter 2:
--
-- (x - g(c))^T(x - g(c)) = x^T x - 2x^T g(c) + g(c)^T g(c)


  -- Question is, how would we write this formally? What do we want egg to find?
