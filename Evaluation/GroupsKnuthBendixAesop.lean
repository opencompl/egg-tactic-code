-- this only works with the nightly 2022-07-13, adding results as comments
import Aesop

theorem inv_inv
  {G: Type}
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), mul a one = a)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), mul a (inv a) = one)
  (x: G)
  : (inv (inv x) = x) := by
  aesop -- aesop: failed to prove the goal after exhaustive search.

theorem inv_mul_cancel_left
  {G: Type}
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), mul a one = a)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), mul a (inv a) = one)
  (x y : G)
  : (mul (inv x) (mul x y)) = y := by
  aesop -- goals accomplished


theorem mul_inv_cancel_left
  {G: Type}
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), mul a one = a)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), mul a (inv a) = one)
  (x y : G)
  : (mul x (mul (inv x) y)) = y := by
  aesop -- goals accomplished

theorem inv_mul
  {G: Type}
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), mul a one = a)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), mul a (inv a) = one)
  (x y : G)
  : (inv (mul x y)) = (mul (inv y) (inv x)) := by
  aesop -- aesop: failed to prove the goal after exhaustive search.

theorem one_inv
  {G: Type}
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), mul a one = a)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), mul a (inv a) = one)
  (x y : G)
  : (inv one) = one := by
  aesop -- aesop: failed to prove the goal after exhaustive search.
