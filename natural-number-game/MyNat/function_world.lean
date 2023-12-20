import MyNat

example (P Q: Type) (p: P) (h: P->Q) : Q := by
  sorry

example : MyNat -> MyNat := by
  sorry

example (P Q R S T U: Type) (p: P) (h: P -> Q) (i: Q-> R) (j: R->S) (k: S->T) (l: T -> U) : U := by
  sorry

example (P Q R S T U: Type) (p: P) (h: P -> Q) (i: Q-> R) (j: R->S) (k: S->T) (l: T -> U) : U := by
  sorry

example (P Q: Type) : (P -> (Q -> P)):= by
  sorry

example (P Q R: Type) : (P -> (Q -> R)) -> ((P->Q)->(P->R)) := by
  sorry

example (P Q F: Type) : (P->Q) -> ((Q->F)->(P->F)):= by
  sorry

example (P Q: Type) : (P -> Q) -> ((Q->empty)->(P->empty)):= by
  sorry

example (A B E F G I J L : Type)
(f1 : A → B) (f2 : B → E) (f5 : E → F) (f8 : F → G) (f9 : G → J)
(f11 : J → I) (f15 : I → L) : A → L := by
  sorry
