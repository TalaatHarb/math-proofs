import MyNat.le
import MyNat.addition_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

open MyNat

lemma one_add_le_self (x : ℕ) : x ≤ 1 + x := by
  rewrite [add_comm]
  exists 1

lemma le_refl (x : ℕ) : x ≤ x := by
  exists 0

theorem le_succ (a b : ℕ) : a ≤ b → a ≤ succ b := by
  intro h
  rewrite [le_iff_exists_add] at h ⊢ 
  cases h with
  | intro c h' => 
    exists (succ c)
    rewrite [add_succ, h']
    rfl

lemma zero_le (a : ℕ) : 0 ≤ a := by
  induction a with
  | zero => exact le_refl zero
  | succ a' ih => 
  apply le_succ
  exact ih

theorem le_trans (a b c : ℕ) 
  (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by 
  cases hab with
  | intro h hab' => 
  cases hbc with
  | intro f hbc' => 
  rewrite [hab', add_assoc] at hbc'
  rewrite [le_iff_exists_add a c]
  exists (h + f)
    
theorem le_antisem (a b : ℕ)
  (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | intro c hbac => 
  cases hba with
  | intro d habd => 
  induction c with
  | zero => 
  rewrite [add_zero] at hbac
  rewrite [hbac]
  rfl
  | succ c' ih => sorry
  

  
  
theorem le_zero (a : ℕ) (h : a ≤ 0) : a = 0 := by
  sorry

theorem le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  sorry

lemma le_succ_self (a : ℕ) : a ≤ succ a := by
  sorry

theorem add_le_add_right (a b : ℕ) : 
  a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  sorry

theorem le_of_succ_le_succ (a b : ℕ) : 
  sorry

theorem not_succ_le_self (a : ℕ) : ¬ (succ a ≤ a) := by
  sorry

theorem add_le_add_left (a b t : ℕ) 
  (h : a ≤ b) : t + a ≤ t + b := by
  sorry

#check LE.le

-- a < b := a ≤ b ∧ ¬ (b ≤ a)
-- a < b := succ(a) ≤ b

lemma lt_aux_one (a b : ℕ) : 
  a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := by
  sorry

lemma lt_aux_two (a b : ℕ) : 
  succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := by
  sorry

lemma lt_iff_succ_le (a b : ℕ) : a < b ↔ succ a ≤ b :=
  sorry