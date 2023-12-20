import MyNat
import MyNat.addition_world

open MyNat

lemma succ_inj (a b: MyNat ): succ a = succ b → a = b := by
  sorry

lemma zero_ne_succ (a: MyNat ) : zero ≠ succ a := by
  sorry

lemma succ_succ_inj (a b: MyNat ) : succ (succ a) = succ (succ b) → a = b := by
  sorry

lemma succ_eq_succ_of_eq (a b : MyNat ) : a = b → succ a = succ b := by
  sorry

lemma succ_eq_succ_iff (a b : MyNat ): a = b ↔ succ a = succ b := by
  sorry

theorem add_right_cancel (a b t: MyNat ): a + t = b + t → a = b := by
  sorry

theorem add_left_cancel (a b t: MyNat ): t + a = t + b → a = b := by
  sorry

theorem add_right_cancel_iff (a b t: MyNat ): a + t = b + t ↔ a = b := by
  sorry

lemma eq_zero_of_add_right_eq_self (a b : MyNat) : a + b = a → b = 0 := by
  sorry

theorem succ_ne_zero (a : MyNat) : succ a ≠ 0 := by
  sorry

lemma add_left_eq_zero (a b : MyNat) (H : a + b = zero) : b = zero := by
  sorry

lemma add_right_eq_zero (a b : MyNat) : a + b = zero → a = zero := by
  sorry

lemma add_one_eq_succ (d : MyNat) : d + 1 = succ d := by
  sorry

lemma ne_succ_self (n : MyNat) : n ≠ succ n := by
  sorry
