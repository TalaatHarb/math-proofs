import MyNat.lemma

open Lean Core

example (P Q: Prop) (p: P) (h: P->Q) : Q :=
  by exact h p

lemma imp_self(P : Prop) : P -> P:=
  by
  intro p
  exact p

lemma maze(P Q R S T U: Prop)
  (p: P) (h: P -> Q) (i: Q-> R) (j: R->S) (k: S->T) (l: T -> U) : U := by
  exact l (k ( j (i (h p))))

example (P Q: Prop) : (P -> (Q -> P)):= by
  intro p _
  exact p

lemma imp_trans (P Q R : Prop) : (P → Q) → ((Q → R) → (P → R)) :=
  by
  intro hpq hqr p
  exact hqr (hpq p)

lemma contrapositive (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
  by
  intro hpq nq p
  apply nq
  exact hpq (p)

example (A B E F G I J L : Prop)
(f1 : A → B) (f2 : B → E) (f5 : E → F) (f8 : F → G) (f9 : G → J)
(f11 : J → I) (f15 : I → L) : A → L :=
  by
  intro a
  exact f15 ( f11 (f9 (f8 (f5 (f2 (f1 (a)))))))

lemma not_iff_imp_false (P : Prop) : ¬ P ← > (P → False) := by
  exact Iff.rfl
