import MyNat

example (P Q: Type) (p: P) (h: P->Q) : Q :=
  by exact h p

example : ℕ -> ℕ :=
  by 
  intro n
  exact n

example (P Q R S T U: Type) 
  (p: P) (h: P -> Q) (i: Q-> R) (j: R->S) (k: S->T) (l: T -> U) : U := by
  have q:= h p
  have r:= i q
  have s:= j r
  have t:= k s
  exact l t

example (P Q R S T U: Type) 
  (p: P) (h: P -> Q) (i: Q-> R) (j: R->S) (k: S->T) (l: T -> U) : U := by
  apply l
  apply k
  apply j
  apply i
  apply h
  exact p

example (P Q: Type) : (P -> (Q -> P)):= by
  intro p _ 
  exact p

example (P Q R: Type) : (P -> (Q -> R)) -> ((P->Q)->(P->R)) := 
  by
  intro a b c
  have q := b c
  have r := a c
  exact r q

example (P Q F: Type) : (P->Q) -> ((Q->F)->(P->F)):=
  by
  intro a b c
  have q:= a c
  exact b q

example (P Q: Type) : (P -> Q) -> ((Q->empty)->(P->empty)):=
  by
  intro a b c
  have q:= a c
  exact b q

example (A B E F G I J L : Type)
(f1 : A → B) (f2 : B → E) (f5 : E → F) (f8 : F → G) (f9 : G → J) 
(f11 : J → I) (f15 : I → L) : A → L :=
  by
  intro a
  exact f15 ( f11 (f9 (f8 (f5 (f2 (f1 (a)))))))



