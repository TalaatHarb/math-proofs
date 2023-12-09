import Goldbach

open Nat

example : even 2 := by
  rfl

example : 3 | 9 := by
  unfold divides
  rfl

theorem no_nat_between_succ (a b: Nat): ¬ (b < a ∧ a < succ b):= by
  intro ⟨ h1, h2⟩
  induction b generalizing a with
  | zero =>
  {
    cases a with
    | zero => contradiction
    | succ a => contradiction
  }
  | succ b ih =>
  {
    cases a with
    | zero => contradiction
    | succ a =>
    have hc1:= Nat.lt_of_succ_lt_succ h1
    have hc2:= Nat.lt_of_succ_lt_succ h2
    exact ih a hc1 hc2
  }

theorem between_succ {a b: Nat}: (b < a ∧ a < succ (succ b)) → a = succ b := by
  intro ⟨ h1, h2⟩
  by_cases h: a = succ b
  . exact h
  . have hc:= Nat.le_of_lt_succ h2
    have he:= Nat.lt_of_le_of_ne hc h
    have hf:= no_nat_between_succ a b
    have hd:= And.intro h1 he
    contradiction

example : prime 2 := by
  unfold prime divides
  constructor
  . trivial
  . intro n h _
    have hc:= no_nat_between_succ n 1
    contradiction

example : prime 3 := by
  unfold prime divides
  constructor
  . trivial
  . intro n h1 h2
    have hc:= between_succ h1
    rw [hc] at h2
    contradiction

example : prime 5 := by
  -- general way to prove primality by testing all numbers
  unfold prime divides
  constructor
  . trivial
  . intro n h1 h3
    cases h1 with
    | intro h1 h2 =>
    cases h2 with
    | refl => contradiction
    | step h =>
    cases h with
    | refl => contradiction
    | step h =>
    cases h with
    | refl => contradiction
    | step h =>
    cases h with
    | refl => contradiction
    | step h =>
    cases h with
    | refl => contradiction
    | step h =>
    contradiction

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

theorem mod_mod (a n : Nat) : (a % n) % n = a % n := by
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero]
  . rw [mod_eq_of_lt,]
    apply mod_lt
    exact nat_gt_zero hn0

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

theorem succ_eq_succ_of_eq (a b : Nat ) : a = b → succ a = succ b := by
  intro hab
  rw [hab]

theorem eq_succ_eq (a b : Nat ) : succ a = succ b → a = b := by
  intro hab
  rw [succ_eq_add_one, succ_eq_add_one] at hab
  exact Nat.add_right_cancel hab

theorem succ_mod (a n : Nat): (succ a) % n = (succ (a % n)) % n:= by
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero, Nat.mod_zero, Nat.mod_zero]
  . by_cases hn1: n = 1
    . rw [hn1, Nat.mod_one, Nat.mod_one]
    .

      sorry

theorem mod_succ {a b n: Nat}: a % n = b % n → (succ a) % n = (succ b) % n:= by
  intro h
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero, Nat.mod_zero] at h
    rw [h]
  . by_cases hn1: n = 1
    . rw [hn1, Nat.mod_one, Nat.mod_one]
    . have hs: (succ (a%n))%n = (succ (b%n))%n := by rw [h]
      rw [← succ_mod,← succ_mod] at hs
      repeat {assumption}

theorem succ_mod_rfl {a b n: Nat}: (succ a) % n = (succ b) % n → a % n = b % n:= by
  intro h
  by_cases hn1: n = 1
  . rw [hn1]
    rw [Nat.mod_one, Nat.mod_one]
  . by_cases hn0 : n = 0
    . rw [hn0] at h
      rw [Nat.mod_zero, Nat.mod_zero] at h
      have hab := eq_succ_eq a b h
      rw[hab]
    .
      sorry


theorem mod_add_left_cancel (a b n t: Nat): (a % n = b % n) ↔ (t+a)%n = (t+b)%n:= by
  constructor
  . intro h
    induction t generalizing a b with
    | zero => rw [Nat.zero_add, Nat.zero_add]; assumption;
    | succ t' ih =>
    rw [succ_eq_add_one, Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1, Nat.add_comm 1]
    apply ih
    apply mod_succ
    assumption
  . intro h
    induction t generalizing a b with
    | zero => rw [Nat.zero_add, Nat.zero_add] at h; assumption
    | succ t' ih =>
    rw [succ_eq_add_one, Nat.add_assoc, Nat.add_assoc] at h
    have hr:= ih (1+a) (1+b) h
    rw [Nat.add_comm 1, Nat.add_comm 1] at hr
    exact succ_mod_rfl hr

theorem succ_zero_mod (a n : Nat)(hn: n ≠ 0 ∧ n ≠ 1)(h: a % n = 0): (succ a) % n = 1:= by
  cases a with
  | zero => rw [succ_eq_add_one, Nat.zero_add, one_mod]; exact hn.right;
  | succ d =>
  rw [succ_mod, h, succ_eq_add_one, Nat.add_zero, one_mod]
  exact hn.right

theorem add_in_mod (a b n: Nat): (a + b) % n = (a + b % n) % n:= by
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero, Nat.mod_zero, Nat.mod_zero]
  . induction b generalizing a with
    | zero => rw [Nat.add_zero, Nat.zero_mod, Nat.add_zero]
    | succ a' ih =>
    rw [succ_eq_add_one, Nat.add_left_comm, Nat.add_comm a', ih (a+1), Nat.add_assoc, ← mod_add_left_cancel, mod_mod, Nat.add_comm a', ih]


theorem add_mod (a b n : Nat): ((a+b)%n = (a%n + b%n) %n):=by
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero, Nat.mod_zero, Nat.mod_zero, Nat.mod_zero]
  . induction b generalizing a with
    | zero => rw [Nat.zero_mod, Nat.add_zero, Nat.add_zero, mod_mod]
    | succ b' ih =>
    rw [Nat.add_succ]
    by_cases h1: n = 1
    . have hl:= Nat.mod_one (succ (a + b'))
      have hr:= Nat.mod_one (a % 1 + succ b' % 1)
      rw [h1, hl, hr]
    . have hr:= ih (succ a)
      rw[Nat.succ_add, ] at hr
      rw [hr, ← mod_mod (succ a), succ_mod, mod_mod, ← ih, Nat.succ_add, Nat.add_comm, ← Nat.succ_add, Nat.add_comm]
      exact add_in_mod (a%n) (succ b') n

theorem factors_divides_left {n a b: Nat}(h: n = a * b)(ha: a ≠ 0 ): a | n := by
  unfold divides
  rw [h]
  clear h
  induction b generalizing a with
  | zero => rw [Nat.mul_zero, Nat.zero_mod]
  | succ b' hb =>
  rw [Nat.mul_succ, add_mod, Nat.mod_self, Nat.add_zero, mod_mod]
  apply hb
  repeat {apply ha}

theorem factors_not_prime (n a b: Nat)(h: n = a * b)(ha: 1 < a)(hn: a < n) : ¬ prime n := by
  by_cases hp: prime n
  . unfold prime at hp
    have hc := (hp.right a) (And.intro ha hn)
    have hz : a ≠ 0 := by exact (Nat.ne_of_lt (Nat.lt_of_succ_lt ha)).symm
    have hf: n % a = 0 := by exact factors_divides_left h hz
    unfold divides at hc
    contradiction
  . assumption


theorem goldbach_conjuctrue :∀ n: Nat, even n ∧ n ≥ 4 → ∃ a b: Nat, (n = a + b) ∧ (prime a) ∧ (prime b) := by
  -- no one knows how to solve this
  sorry

theorem equivalent_goldbach: ∀ n: Nat, n > 3 → ∃ k: Nat, k < n ∧ prime (n - k) ∧ prime (n + k):= by
  -- no one knows how to solve this
  -- this is the important insight behind it, since it corresponds to prime numbers distribution
  sorry
