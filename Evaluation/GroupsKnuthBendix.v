Theorem inv_inv
  {G: Type}
  (inv: G -> G)
  (mul: G -> G -> G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), one = mul a (inv a))
  (x: G)
  : (inv (inv x) = x).
Proof.
  try congruence with assocMul invLeft mulOne oneMul invRight.
  Admitted.

Theorem inv_mul_cancel_left
  {G: Type}
  (inv: G -> G)
  (mul: G -> G -> G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), one = mul a (inv a))
  (x y : G)
  : (mul (inv x) (mul x y)) = y.
Proof.
  try congruence with assocMul invLeft mulOne oneMul invRight.
Qed.

Theorem mul_inv_cancel_left
  {G: Type}
  (inv: G -> G)
  (mul: G -> G -> G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), one = mul a (inv a))
  (x y : G)
  : (mul x (mul (inv x) y)) = y.
Proof.
  try congruence with assocMul invLeft mulOne oneMul invRight.
Qed.

Theorem inv_mul
  {G: Type}
  (inv: G -> G)
  (mul: G -> G -> G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), one = mul a (inv a))
  (x y : G)
  : (inv (mul x y)) = (mul (inv y) (inv x)).
Proof.
  try congruence with assocMul invLeft mulOne oneMul invRight.
Admitted.

Theorem one_inv
  {G: Type}
  (inv: G -> G)
  (mul: G -> G -> G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (oneMul: forall (a: G), mul one a = a)
  (invRight: forall (a: G), one = mul a (inv a))
  (x y : G)
  : (inv one) = one.
Proof.
  try congruence with assocMul invLeft mulOne oneMul invRight.
Qed.
