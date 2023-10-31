import MyNat
import MyNat.lemma
import MyNat.tutorial_world

open MyNat

lemma zero_add (n: MyNat) :
  zero + n = n :=
  by
  induction n with
    | zero => rfl
    | succ n' ih => rw [add_succ, ih]

lemma add_assoc (a b c: MyNat) :
  (a + b) + c = a + (b + c) :=
  by induction c with
  | zero => rfl
  | succ c' ih => rw [add_succ, add_succ, add_succ, ih]

lemma succ_add (a d: MyNat) : succ (d) + a = succ (d + a) :=
  by induction a with
  | zero => rw [add_zero, add_zero]
  | succ a' ih => rw [add_succ, add_succ, ih]

lemma add_comm (a b: MyNat) : a + b = b + a :=
  by induction b with
  | zero => rw [add_zero, zero_add]
  | succ b' ih => rw [succ_add, add_succ, ih]

lemma one_eq_succ_zero : 1 = succ (zero) := rfl
lemma two_eq_succ_one : 2 = succ (1) := rfl

lemma succ_eq_add_one (a: MyNat) : succ (a) = a + 1 :=
  by induction a with
  | zero => rfl
  | succ a' ih => rw [succ_add, ih]

lemma add_right_comm (a b c: MyNat) : a + b + c = a + c + b :=
  by rw [add_assoc, add_comm b c, <- add_assoc]

lemma zero_equal_numeral : zero = 0 := rfl
