import MyNat
import MyNat.lemma
import MyNat.le
import MyNat.addition_world
import MyNat.advanced_addition_world

open MyNat

lemma one_add_le_self (x : MyNat) : x ≤ 1 + x := by
  rw [add_comm]
  exists 1

lemma le_refl (x : MyNat) : x ≤ x := by
  exists 0

theorem le_succ (a b : MyNat) : a ≤ b → a ≤ succ b := by
  intro h
  rw [le_iff_exists_add] at h ⊢
  cases h with
  | intro c h' =>
    exists (succ c)
    rw [add_succ, h']

lemma zero_le (a : MyNat) : 0 ≤ a := by
  induction a with
  | zero => exact le_refl zero
  | succ a' ih =>
  apply le_succ
  exact ih

theorem le_trans (a b c : MyNat)
  (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | intro h hab' =>
  cases hbc with
  | intro f hbc' =>
  rw [hab', add_assoc] at hbc'
  rw [le_iff_exists_add a c]
  exists (h + f)

theorem le_antisem (a b : MyNat)
  (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | intro c1 hab =>
  cases hba with
  | intro c2 hba =>
  rw [hab, add_assoc] at hba
  have hc := eq_zero_of_add_right_eq_self a (c1+c2) (Eq.symm hba)
  have hc1 := add_right_eq_zero c1 c2 hc
  rw [hc1, add_zero a] at hab
  exact Eq.symm hab

theorem le_zero (a : MyNat) (h : a ≤ 0) : a = 0 := by
  cases h with
  | intro c hac =>
  have hc := add_right_eq_zero a c (Eq.symm hac)
  exact hc

theorem not_le_reverse (a b: MyNat) (h: ¬a ≤ b) : b ≤ a := by
  by_cases hba : b ≤ a
  exact hba

  sorry

theorem le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  by_cases h : a ≤ b
  exact Or.inl h
  exact Or.inr (not_le_reverse a b h)

lemma le_succ_self (a : MyNat) : a ≤ succ a := by
  rw [le_iff_exists_add, succ_eq_add_one]
  exists 1

theorem add_le_add_right (a b : MyNat) :
  a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h t
  cases h with
  | intro c hc =>
  exists c
  rw[hc, add_right_comm]

theorem le_of_succ_le_succ (a b : MyNat) :
  succ a ≤ succ b → a ≤ b := by
  rw [succ_eq_add_one, succ_eq_add_one, add_comm, add_comm b]
  intro h
  rw [le_iff_exists_add] at h
  cases h with
  | intro c h =>
  rw [add_assoc] at h
  have hp := add_left_cancel b (a+c) 1 h
  have p : ∃ (c : MyNat), b = a + c := Exists.intro c hp
  rw [← le_iff_exists_add] at p
  exact p

theorem not_succ_le_self (a : MyNat) : ¬ (succ a ≤ a) := by
  sorry

theorem add_le_add_left (a b t : MyNat)
  (h : a ≤ b) : t + a ≤ t + b := by
  rw [le_iff_exists_add] at h
  cases h with
  | intro c h =>
  rw [h, ← add_assoc]
  exists c

lemma lt_aux_one (a b : MyNat) :
  a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := by
  sorry

lemma lt_aux_two (a b : MyNat) :
  succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := by
  sorry

lemma lt_iff_succ_le (a b : MyNat) : a < b ↔ succ a ≤ b :=
  sorry
