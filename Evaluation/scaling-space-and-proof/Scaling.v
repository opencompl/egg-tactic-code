Inductive B := 
| O | I.
  
Theorem count_upward_v3: forall
    (count: B -> B -> B -> B)
    (count_0: forall (b2 b1: B), count b2 b1 O = count b2 b1 I)
    (count_1: forall (b2: B), count b2 O I = count b2 I O)
    (count_2: count O I I = count I O O), count I I I = count O O O.
Proof.
  intros.
  congruence.
Qed.

