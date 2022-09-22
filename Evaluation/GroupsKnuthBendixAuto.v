Parameter G : Type.
Parameter inv: G -> G.
Parameter mul: G -> G -> G.
Parameter one: G.
Axiom  assocMul : forall (a b c: G), mul a (mul b c) = (mul (mul a b) c).
Axiom invLeft: forall (a: G), mul (inv a) a = one.
Axiom oneMul: forall (a: G), mul one a = a.
Axiom mulOne: forall (a: G), mul a one = a.
Axiom invRight: forall (a: G), mul a (inv a) = one.
Global Hint Rewrite assocMul invLeft mulOne oneMul invRight : base0.

Theorem inv_mul_cancel_left
  (x y : G)
  : (mul (inv x) (mul x y)) = y.
Proof.
  try autorewrite with base0. reflexivity. Qed.

Theorem mul_inv_cancel_left
  (x y : G)
  : (mul x (mul (inv x) y)) = y.
Proof.
  try autorewrite with base0. reflexivity. Qed.

Theorem inv_mul
  (x y : G)
  : (inv (mul x y)) = (mul (inv y) (inv x)).
Proof.
  try autorewrite with base0. Admitted.

Theorem one_inv
  (x y : G)
  : (inv one) = one.
Proof.
  try autorewrite with base0. Admitted.

Theorem inv_inv
  (x: G)
  : (inv (inv x) = x).
Proof.
 try autorewrite with base0. Admitted.
