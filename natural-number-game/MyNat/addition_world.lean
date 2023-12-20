import MyNat
import MyNat.lemma
import MyNat.tutorial_world

open MyNat

lemma zero_add (n: MyNat) : zero + n = n := by
  sorry

lemma add_assoc (a b c: MyNat) : (a + b) + c = a + (b + c) := by
  sorry

lemma succ_add (a d: MyNat) : succ (d) + a = succ (d + a) := by
  sorry

lemma add_comm (a b: MyNat) : a + b = b + a := by
  sorry

lemma one_eq_succ_zero : 1 = succ (zero) := by
  sorry

lemma two_eq_succ_one : 2 = succ (1) := by
  sorry

lemma succ_eq_add_one (a: MyNat) : succ (a) = a + 1 := by
  sorry

lemma add_right_comm (a b c: MyNat) : a + b + c = a + c + b := by
  sorry

lemma zero_equal_numeral : zero = 0 := by
  sorry
