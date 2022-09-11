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
  simp [assocMul, invLeft, mulOne, oneMul, invRight]

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
  simp [assocMul, invLeft, mulOne, oneMul, invRight]


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
  simp [assocMul, invLeft, mulOne, oneMul, invRight]


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
  simp [assocMul, invLeft, mulOne, oneMul, invRight]

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
  simp [assocMul, invLeft, mulOne, oneMul, invRight]
