import MyNat
import MyNat.lemma
import MyNat.le
import MyNat.addition_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

open MyNat

lemma one_add_le_self (x : MyNat) : x ≤ 1 + x := by
  sorry

lemma le_refl (x : MyNat) : x ≤ x := by
  sorry

theorem le_succ (a b : MyNat) : a ≤ b → a ≤ succ b := by
  sorry

lemma zero_le (a : MyNat) : zero ≤ a := by
  sorry

theorem le_trans (a b c : MyNat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  sorry

theorem le_antisem (a b : MyNat) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  sorry

theorem le_zero (a : MyNat) (h : a ≤ 0) : a = 0 := by
  sorry

theorem le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  sorry

theorem not_le_reverse_lt (a b: MyNat) (h: ¬a ≤ b) : b < a := by
  sorry

theorem not_le_reverse (a b: MyNat) (h: ¬a ≤ b) : b ≤ a := by
  sorry

lemma le_succ_self (a : MyNat) : a ≤ succ a := by
  sorry

theorem add_le_add_right (a b : MyNat) : a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  sorry

theorem le_of_succ_le_succ (a b : MyNat) : succ a ≤ succ b → a ≤ b := by
  sorry

theorem not_succ_le_self (a : MyNat) : ¬ (succ a ≤ a) := by
  sorry

theorem add_le_add_left (a b t : MyNat) (h : a ≤ b) : t + a ≤ t + b := by
  sorry

lemma lt_aux_one (a b : MyNat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := by
  sorry

lemma lt_aux_two (a b : MyNat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := by
  sorry

lemma lt_iff_succ_le (a b : MyNat) : a < b ↔ succ a ≤ b := by
  sorry
