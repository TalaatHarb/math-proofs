import MyNat
import MyNat.multiplication_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

open MyNat

theorem mul_pos (a b : MyNat) : a ≠ zero → b ≠ zero → a * b ≠ zero := by
  sorry

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : MyNat) (h : a * b = zero) : a = zero ∨ b = zero := by
  sorry

theorem mul_eq_zero_iff (a b : MyNat) : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  sorry

theorem mul_left_cancel (a b c : MyNat) (ha : a ≠ zero) : a * b = a * c → b = c := by
  sorry
