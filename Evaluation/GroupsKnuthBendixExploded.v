Theorem inv_inv
  {G: Type}
  (inv: G -> G)
  (mul: G -> G -> G)
  (one: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (assocMul': forall (a b c: G), (mul (mul a b) c) = mul a (mul b c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (invLeft': forall (a: G), one = mul (inv a) a)
  (mulOne: forall (a: G), a = mul a one)
  (mulOne': forall (a: G), mul a one = a)
  (oneMul: forall (a: G), mul one a = a)
  (oneMul': forall (a: G), a = mul one a)
  (invRight: forall (a: G), one = mul a (inv a))
  (invRight': forall (a: G), mul a (inv a) = one)
  (x: G)
  (invRightx : mul x (inv x) = one)
  (invRightOne : mul one (inv one) = one)
  (invRightx' : one = mul x (inv x))
  (invRightOne' : one = mul one (inv one))
  : (inv (inv x) = x).
Proof.
  try congruence with assocMul assocMul' invLeft invLeft' mulOne mulOne' oneMul oneMul' invRight invRightx invRightx' invRightOne invRightOne'.
  Qed.

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
  (assocMul': forall (a b c: G), (mul (mul a b) c) = mul a (mul b c))
  (invLeft': forall (a: G), one = mul (inv a) a)
  (mulOne': forall (a: G), mul a one = a)
  (oneMul': forall (a: G), a = mul one a)
  (invRight': forall (a: G), mul a (inv a) = one)
  (invRightx : mul x (inv x) = one)
  (invRightOne : mul one (inv one) = one)
  (invRightx' : one = mul x (inv x))
  (invRightOne' : one = mul one (inv one))
  (invRighty : mul y (inv y) = one)
  (invRighty' : one = mul y (inv y))
  : (inv (mul x y)) = (mul (inv y) (inv x)).
Proof.
  try congruence with assocMul assocMul' invLeft invLeft' mulOne mulOne' oneMul oneMul' invRight invRightx invRightx' invRightOne invRightOne' invRighty invRighty'.
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
