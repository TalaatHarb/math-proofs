import MyNat
import MyNat.lemma
import MyNat.tutorial_world

open MyNat

lemma zero_add (n: MyNat) :
  zero + n = n := 
  by
  induction n with
    | zero => rfl
    | succ n' ih => rewrite [add_succ, ih] rfl

lemma add_assoc (a b c: MyNat) :
  (a + b) + c = a + (b + c) :=
  by induction c with
  | zero => rewrite [add_zero] rfl
  | succ c' ih => rewrite [add_succ, add_succ, add_succ, ih] rfl
  
lemma succ_add (a d: MyNat) : succ (d) + a = succ (d + a) :=
  by induction a with
  | zero => rewrite [add_zero, add_zero] rfl
  | succ a' ih => rewrite [add_succ, add_succ, ih] rfl

lemma add_comm (a b: MyNat) : a + b = b + a :=
  by induction b with
  | zero => rewrite [add_zero, zero_add] rfl
  | succ b' ih => rewrite [succ_add, add_succ, ih] rfl

lemma one_eq_succ_zero : 1 = succ (zero) := rfl
lemma two_eq_succ_one : 2 = succ (1) := rfl

lemma succ_eq_add_one (a: MyNat) : succ (a) = a + 1 :=
  by induction a with
  | zero => rewrite [zero_add] rfl
  | succ a' ih => rewrite [succ_add, ih] rfl

lemma add_right_comm (a b c: MyNat) : a + b + c = a + c + b :=
  by rewrite [add_assoc, add_comm b c, <- add_assoc] rfl

lemma zero_equal_numeral : zero = 0 := rfl
