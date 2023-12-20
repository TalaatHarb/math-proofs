import MyNat.lemma

example (P Q: Prop) (p: P) (h: P->Q) : Q := by
  sorry

lemma imp_self(P : Prop) : P -> P:= by
  sorry

lemma maze(P Q R S T U: Prop) (p: P) (h: P -> Q) (i: Q-> R) (j: R->S) (k: S->T) (l: T -> U) : U := by
  sorry

example (P Q: Prop) : (P -> (Q -> P)):= by
  sorry

lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) := by
  sorry

lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  sorry

example (A B E F G I J L : Prop)
(f1 : A → B) (f2 : B → E) (f5 : E → F) (f8 : F → G) (f9 : G → J)
(f11 : J → I) (f15 : I → L) : A → L := by
  sorry

lemma not_iff_imp_false (P : Prop) : ¬ P → (P → False) := by
  sorry
