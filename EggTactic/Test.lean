import EggTactic

set_option trace.EggTactic.egg true
-- TODO @andres: what egg gives us back is wrong. What we really need
-- to know is the rewrite term that we need to use.  This means we
-- should build the sexpr (<rewrite-term> <arg-1> ... <arg-n>) and
-- then use this to perform the rewrite.  Instead, what `egg` gives us
-- is the goal state after the rewrite.  This is a problem because we
-- need to know the rewrite term to perform the rewrite.  We can't
-- just use the goal state because the goal state is the result of the
-- rewrite.


theorem testRfl (anat: Nat) (bnat: Nat) (H: anat = bnat): anat = bnat := by {
  intros;
  eggxplosion [H]
}

#print testRfl


theorem testSym (anat: Nat) (bnat: Nat) (H: anat = bnat): bnat = anat := by {
  intros;
  eggxplosion [H]
}

#print testSym


theorem testTrans (anat bnat cnat : Nat) (H : bnat = anat) (K : cnat = bnat)
  : anat = cnat := by {
  intros;
  eggxplosion [H, K]
}

#print testTrans


set_option pp.analyze true in
theorem testSuccess (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint): bint = eint := by
  --  eggxplosion [not_rewrite]
  --  eggxplosion [rewrite_wrong_type]
  -- rewrite [b_eq_d]
  -- rewrite [d_eq_e]
  -- rfl
  eggxplosion [b_eq_d, d_eq_e]

#print testSuccess


theorem testSuccess0Symm (anat: Nat) (bnat: Nat) (H: bnat = anat): anat = bnat := by {
  intros;
  eggxplosion [H]
}

#print testSuccess0Symm


theorem testApp1 (anat bnat : Nat) (H : anat = bnat)
  (f : Nat → Nat) : f anat = f bnat := by {
  eggxplosion [H]
}
-- elab "boiledEgg" "[" rewrites:ident,* "]" : tactic =>  withMainContext  do

-- | test that we can run rewrites



-- | test that we can run theorems in reverse.
theorem testSuccessRev : ∀ (anat: Nat) (bint: Int) (cnat: Nat)
  (dint: Int) (eint: Int) (a_eq_a: anat = anat) (b_eq_d: bint = dint) (d_eq_e: dint = eint),
  eint = bint := by
   intros a b c d e aeqa beqd deqe
   eggxplosion [beqd, deqe]

#print testSuccessRev



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
  eggxplosion [gh, gk]

#print testManualInstantiation
-/


theorem assoc_instantiate(G: Type)
  (mul: G → G → G)
  (assocMul: forall (a b c: G), (mul (mul a b) c) = mul a (mul b c))
  (x y z: G) : mul x (mul y z) = mul (mul x y) z := by {
  eggxplosion [assocMul]
}

#print assoc_instantiate


/-
theorem testGoalNotEqualityMustFail : ∀ (a: Nat) (b: Int) (c: Nat) , Nat := by
 intros a b c
 eggxplosion []
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
  --(invRightX: one = mul x (inv x))
  : (inv (inv x) = x) := by
  eggxplosion [assocMul, invLeft, mulOne, invRight] (timeLimit := 3)

#print inv_mul_cancel_left

def all {α  : Type} (p : α → Bool) (xs : List α) := List.and (List.map p xs)
def all'{α  : Type} (p : α → Bool) (xs : List α) := List.foldr (λ a b => b && (p a)) True xs

theorem deforestation : ∀ (p : α → Bool) (xs : List α), all p xs = all' p xs := by
  intros p xs
  unfold all
  unfold all'
  unfold List.map
  unfold List.and
  unfold List.all
  induction xs with
    | nil =>
      simp
      rfl
    | cons head tail ih =>
      -- ⊢ List.foldr (fun a r => a && r) true (p head :: List.map p tail) = List.foldr (fun a b => b && p a) true (head :: tail)




theorem testInstantiation
  -- TODO: need to change definitions to make all arguments implicit, since those are the only kinds of rewrites
  -- egg can cope with!
  (group_inv: forall {g: Int}, g - g  = 0)
  (h: Int) (k: Int): h - h = k - k := by {
   -- expected no bound variables, we use locally nameless.
   -- @andres: I strongly suspect the toExplode
   -- array somehow leaking in `bvars` on accident. A cursory glance at it did not show me what it
   -- does when it doesn't explode a variable; I would have expected it to instantiate an `mvar`.
   eggxplosion [group_inv];
}


#print testInstantiation
