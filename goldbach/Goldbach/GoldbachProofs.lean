import Goldbach

open Nat

example : even 2 := by
  rfl

example : 3 | 9 := by
  unfold divides
  rfl

theorem nat_gt_zero {a : Nat} (h: a ≠ 0) : a > 0:= by
  by_cases ha: a ≤ 0
  . rw [le_zero_eq] at ha
    contradiction
  . apply gt_of_not_le ha

theorem le_zero {n: Nat} (h: n ≤ 0): n = 0 := by
  cases h with
  | refl =>
  rfl

theorem le_one {n: Nat} (h: n ≤ 1): n = 0 ∨ n = 1:= by
  cases h with
  | step h => have hr:=le_zero h; apply Or.inl ; assumption
  | refl => apply Or.inr; rfl

theorem one_mod {n: Nat} (h1: n ≠ 1): 1 % n = 1:= by
  by_cases h: 1 < n
  . rw [mod_eq_of_lt]; assumption
  . rw [not_lt_eq] at h
    have hn := le_one h
    cases hn with
    | inl hn => rw [hn]; rfl
    | inr hn => contradiction

theorem mod_mod (a n : Nat) (hn: n ≠ zero) : (a % n) % n = a % n := by
  rw [mod_eq_of_lt,]
  apply mod_lt
  exact nat_gt_zero hn

theorem mul_two_even (a: Nat) : even (a * 2):= by
  unfold even divides
  induction a with
  | zero => rfl
  | succ a ih =>
  rw [succ_eq_add_one, Nat.add_mul, Nat.one_mul]
  rw [mod_eq_sub_mod]
  exact ih
  apply le_add_left

theorem two_mul_even (a: Nat) : even (2 * a):= by
  rw [Nat.mul_comm]
  exact mul_two_even a

theorem powers_of_2_even (n: Nat) (h: n ≠ zero): even (2 ^ n):= by
  cases n with
  | zero => contradiction
  | succ n =>
  rw [pow_succ]
  exact mul_two_even (2 ^ n)

theorem even_is_mul_two {a: Nat} (ha: even a) : ∃ k : Nat, a = 2 * k:= by

  sorry

theorem odd_not_mul_two {a: Nat} (ha: odd a) : ¬ ∃ k : Nat, a = 2 * k:= by

  sorry

theorem succ_even {a : Nat}(ha: even a): odd (succ a):= by
  have h:= even_is_mul_two ha

  sorry

theorem odd_pattern {a: Nat} (ha: odd a) : ∃ k : Nat, a = 2 * k + 1:= by

  sorry

theorem succ_odd {a : Nat}(ha: odd a): even (succ a):= by
  sorry

theorem even_plus_even {a b: Nat} (h: even a ∧ even b): even (a + b):= by
  have ha:= h.left
  have hb:= h.right

  sorry

theorem even_plus_odd {a b: Nat} (h: even a ∧ odd b): odd (a + b):= by
  have ha:= h.left
  have hb:= h.right

  sorry

theorem odd_plus_odd {a b: Nat} (h: odd a ∧ odd b): even (a + b):= by
  have ha:= h.left
  have hb:= h.right

  sorry

theorem odd_plus_even {a b: Nat} (h: odd a ∧ even b): odd (a + b):= by

  sorry

theorem goldbach_conjuctrue (n: Nat)(he: even n)(h2: n ≥ 2) : ∃ a b: Nat, (n = a + b) ∧ (prime a) ∧ (prime b) := by
  -- no one knows how to solve this
  sorry
