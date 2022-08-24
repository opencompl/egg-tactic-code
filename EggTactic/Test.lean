import EggTactic

theorem testSuccess0 (anat: Nat) (bnat: Nat) (H: anat = bnat): anat = bnat := by {
  intros;
  rawEgg [H]
}

#print testSuccess0


set_option pp.analyze true in
theorem testSuccess (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint): bint = eint := by
  --  rawEgg [not_rewrite]
  --  rawEgg [rewrite_wrong_type]
  -- rewrite [b_eq_d]
  -- rewrite [d_eq_e]
  -- rfl
  rawEgg [b_eq_d, d_eq_e]


#print testSuccess


theorem testSuccess0Symm (anat: Nat) (bnat: Nat) (H: bnat = anat): anat = bnat := by {
  intros;
  rawEgg [H]
}

#print testSuccess0Symm

-- elab "boiledEgg" "[" rewrites:ident,* "]" : tactic =>  withMainContext  do

-- | test that we can run rewrites



-- | test that we can run theorems in reverse.
theorem testSuccessRev : ∀ (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint),
  eint = bint := by
   intros a b c d e aeqa beqd deqe
   rawEgg [beqd, deqe]

#print testSuccessRev


-- {"request":"perform-rewrite","target-lhs":"(ap (ap (ap (ap (ap (ap HSub.hSub Int) Int) Int) (ap (ap instHSub Int) Int.instSubInt)) _uniq.350) _uniq.350)","target-rhs":"(ap (ap (ap (ap (ap (ap HSub.hSub Int) Int) Int) (ap (ap instHSub Int) Int.instSubInt)) _uniq.351) _uniq.351)","rewrites":[]}
theorem testInstantiation
  (group_inv: forall (g: Int), g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by
 rawEgg [group_inv]



#print testInstantiation

/-
theorem testManualInstantiation
(group_inv: forall (g: Int), g - g  = 0)
(h: Int) (k: Int): h - h = k - k := by
  have gh : h - h = 0 := group_inv h
  have gk : k - k = 0 := group_inv k
  -- TODO: figure out how to get these
  -- manually instantiated locals to work.
  -- @bollu's hypothesis is that we need to force
  -- metavariable resolution at the value and type level
  -- with a couple 'reduce's.
  rawEgg [gh, gk]

#print testManualInstantiation
-/


theorem assoc_instantiate(G: Type)
  (mul: G → G → G)
  (assocMul: forall (a b c: G), (mul (mul a b) c) = mul a (mul b c))
  (x y z: G) : mul x (mul y z) = mul (mul x y) z := by {
  rawEgg [assocMul]
}

#print assoc_instantiate


/-
theorem testGoalNotEqualityMustFail : ∀ (a: Nat) (b: Int) (c: Nat) , Nat := by
 intros a b c
 rawEgg []
 sorry
-/



/-
      rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
      rw!("assoc-mul'"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
      rw!("one-mul";  "(* 1 ?a)" => "?a"),
      rw!("one-mul'";  "?a" => "(* 1 ?a)"),
      rw!("inv-left";  "(* (^-1 ?a) ?a)" => "1"),
      rw!("inv-left'";  "1" => "(* (^-1 a) a)"),
      rw!("inv-left''";  "1" => "(* (^-1 b) b)"),
      rw!("mul-one";  "(* ?a 1)" => "?a"),
      rw!("mul-one'";  "?a" => "(* ?a 1)" ),
      rw!("inv-right";  "(* ?a (^-1 ?a))" => "1"),
      rw!("inv-right'";  "1" => "(* a (^-1 a))"),
      rw!("inv-right''";  "1" => "(* b (^-1 b))"),
      //rw!("anwser''";  "(* (^-1 b)(^-1 a))" => "ANSWER"),
-/
theorem inv_mul_cancel_left (G: Type)
  (inv: G → G)
  (mul: G → G → G)
  (one: G)
  (x: G)
  (assocMul: forall (a b c: G), mul a (mul b c) = (mul (mul a b) c))
  (invLeft: forall (a: G), mul (inv a) a = one)
  (mulOne: forall (a: G), a = mul a one)
  (invRight: forall (a: G), one = mul a (inv a))
  : (inv (inv x) = x) := by {
  rawEgg [assocMul, invLeft, mulOne, invRight]

}
#print inv_mul_cancel_left
