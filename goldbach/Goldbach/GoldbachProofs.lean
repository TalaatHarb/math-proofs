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

theorem mul_two_even (k: Nat) : even (k * 2):= by
  unfold even divides
  induction k with
  | zero => rfl
  | succ k ih =>
  rw [succ_eq_add_one, Nat.add_mul, Nat.one_mul, mod_eq_sub_mod]
  exact ih
  apply le_add_left

theorem two_mul_even (k: Nat) : even (2 * k):= by
  rw [Nat.mul_comm]
  exact mul_two_even k

theorem not_mul_two_odd (k: Nat) : odd (2 * k + 1):= by
  unfold odd divides
  induction k with
  | zero => rw [Nat.mul_zero, Nat.zero_add]; trivial
  | succ k ih =>
  have he: 1 + 1 = 2 * 1 := by trivial
  rw [Nat.mul_succ, Nat.succ_add, succ_eq_add_one, Nat.add_assoc, Nat.add_comm 2 _, ← Nat.add_assoc, mod_eq_sub_mod]
  exact ih
  apply le_add_left

theorem powers_of_2_even (n: Nat) (h: n ≠ zero): even (2 ^ n):= by
  cases n with
  | zero => contradiction
  | succ n =>
  rw [pow_succ]
  exact mul_two_even (2 ^ n)

theorem non_mul_two_odd (a: Nat) : odd (2 * a + 1):= by
  unfold odd divides
  intro h
  induction a with
  | zero => rw [Nat.mul_zero, Nat.zero_add] at h; contradiction
  | succ a ih =>
  rw [succ_eq_add_one, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 2 1, ← Nat.add_assoc, mod_eq_sub_mod] at h
  exact ih h
  apply le_add_left

theorem odd_not_even {a: Nat} : odd a ↔ ¬even a:= by
  constructor
  . intro h
    exact h
  . intro h
    exact h

theorem not_not {P: Prop} : ¬ ¬ P → P:= by
  intro h
  by_cases hp: P
  . exact hp
  . contradiction

theorem even_not_odd {a: Nat} : even a ↔ ¬odd a:= by
  constructor
  . intro he ho
    contradiction
  . intro h
    exact not_not h

theorem nat_odd_or_even {a: Nat} : odd a ∨ even a := by
  by_cases h: even a
  . exact Or.inr h
  . exact Or.inl h

theorem nat_pattern (a: Nat) : (∃ k: Nat, a = 2 * k) ∨ (∃ k: Nat, a = 2 * k + 1):= by
  induction a with
  | zero => apply Or.inl; exists zero;
  | succ a ih =>
  cases ih with
  | inl h =>
  {
    cases h with
    | intro d h =>
    rw [h]
    apply Or.inr
    exists d
  }
  | inr h =>
  {
    cases h with
    | intro d h =>
    rw [h]
    apply Or.inl
    exists (d+1)
  }

theorem even_is_mul_two {a: Nat} (ha: even a) : ∃ k : Nat, a = 2 * k:= by
  have h:= nat_pattern a
  cases h with
  | inl hk => assumption
  | inr hk =>
  {
    cases hk with
    | intro k hk =>
    have hc := not_mul_two_odd k
    rw [hk.symm] at hc
    contradiction
  }


theorem odd_not_mul_two {a: Nat} (ha: odd a) : ¬ ∃ k : Nat, a = 2 * k:= by
  have h:= nat_pattern a
  cases h with
  | inl hk =>
  {
    cases hk with
    | intro k hk =>
    have hc:= two_mul_even k
    rw [hk.symm] at hc
    contradiction
  }
  | inr hk =>
  {
    cases hk with
    | intro k hk =>
    intro h
    cases h with
    | intro d hd =>
    have hc:= two_mul_even d
    rw [hd.symm] at hc
    contradiction
  }

theorem odd_pattern {a: Nat} (ha: odd a) : ∃ k : Nat, a = 2 * k + 1:= by
  have h:= nat_pattern a
  cases h with
  | inr _ => assumption
  | inl h =>
  cases h with
  | intro k hk =>
  have hc:= two_mul_even k
  rw [hk.symm] at hc
  contradiction

theorem succ_even {a : Nat}(ha: even a): odd (succ a):= by
  have h:= even_is_mul_two ha
  cases h with
  | intro k hk =>
  rw [hk, succ_eq_add_one]
  exact non_mul_two_odd k

theorem succ_odd {a : Nat}(ha: odd a): even (succ a):= by
  have h:= odd_pattern ha
  cases h with
  | intro k hk =>
  have he: 1 + 1 = 2 * 1:= by trivial
  rw [hk, succ_eq_add_one, Nat.add_assoc, he, ← Nat.mul_add]
  exact two_mul_even (k+1)

theorem even_plus_even {a b: Nat} (h: even a ∧ even b): even (a + b):= by
  have ha:= even_is_mul_two h.left
  have hb:= even_is_mul_two h.right
  cases ha with
  | intro c hc =>
  cases hb with
  | intro d hd =>
  rw [hc, hd, ← Nat.mul_add]
  exact two_mul_even (c+d)

theorem even_plus_odd {a b: Nat} (h: even a ∧ odd b): odd (a + b):= by
  have ha:= even_is_mul_two h.left
  have hb:= odd_pattern h.right
  cases ha with
  | intro c hc =>
  cases hb with
  | intro d hd =>
  rw [hc, hd, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm, ← Nat.mul_add, Nat.add_comm]
  exact not_mul_two_odd (d+c)

theorem odd_plus_odd {a b: Nat} (h: odd a ∧ odd b): even (a + b):= by
  have ha:= odd_pattern h.left
  have hb:= odd_pattern h.right
  cases ha with
  | intro c hc =>
  cases hb with
  | intro d hd =>
  have he: 1 + 1 = 2 * 1:= by trivial
  rw [hc, hd, Nat.add_left_comm, Nat.add_assoc, he, ← Nat.mul_add, ← Nat.mul_add]
  exact two_mul_even (d + (c + 1))

theorem odd_plus_even {a b: Nat} (h: odd a ∧ even b): odd (a + b):= by
  have ha:= odd_pattern h.left
  have hb:= even_is_mul_two h.right
  cases ha with
  | intro c hc =>
  cases hb with
  | intro d hd =>
  rw [hc, hd, Nat.add_assoc, Nat.add_left_comm, ←Nat.mul_add, Nat.add_comm]
  exact not_mul_two_odd (c+d)

theorem goldbach_conjuctrue (n: Nat)(he: even n)(h2: n ≥ 2) : ∃ a b: Nat, (n = a + b) ∧ (prime a) ∧ (prime b) := by
  -- no one knows how to solve this
  sorry
