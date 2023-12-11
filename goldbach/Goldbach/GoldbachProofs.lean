import Goldbach

open Nat

theorem even_2 : even 2 := by
  rfl

theorem odd_5 : odd 5 := by
  unfold odd divides
  intro
  contradiction

theorem odd_7 : odd 7 := by
  unfold odd divides
  intro
  contradiction

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

theorem prime_2: prime 2 := by
  unfold prime divides
  constructor
  . trivial
  . intro n h _
    have hc:= no_nat_between_succ n 1
    contradiction

theorem prime_3 : prime 3 := by
  unfold prime divides
  constructor
  . trivial
  . intro n h1 h2
    have hc:= between_succ h1
    rw [hc] at h2
    contradiction

theorem prime_5 : prime 5 := by
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

theorem one_plus_one : 1 + 1 = 2 := by trivial

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

theorem not_and {P Q : Prop} : ¬(P ∧ Q) → (¬P) ∨ (¬Q) := by
  intro h
  by_cases hp : P
  . by_cases hq : Q
    . have hpq := And.intro hp hq
      contradiction
    . exact Or.inr hq
  . by_cases hq : Q
    . exact Or.inl hp
    . exact Or.inl hp

theorem multiple_mod (k n: Nat): (k * n) % n = 0 := by
  by_cases hn1: n = 1
  . rw [hn1, Nat.mod_one]
  . induction k with
    | zero => rw [Nat.zero_mul, Nat.zero_mod]
    | succ k' ih =>
    rw [Nat.succ_mul, Nat.mod_eq]
    split
    . next hn =>
      rw [Nat.add_sub_cancel, ih]
    . next hn =>
      have hf := not_and hn
      cases hf with
      | inl hn0 => {
        rw [Nat.not_gt_eq] at hn0
        cases hn0 with
        | refl => rw [Nat.mul_zero, Nat.add_zero]
      }
      | inr hk =>
      have hc:= Nat.le_add_left n (k'*n)
      contradiction

theorem non_multiple_mod (k n d: Nat)(hd: d > 0 ∧ d < n)(hn1: n ≠ 1): (k * n + d) % n ≠ 0 := by
  by_cases hn0: n = 0
  . rw [hn0, Nat.mul_zero, Nat.zero_add, Nat.mod_eq]
    split
    . next hz =>
      have hz0:= hz.left
      contradiction
    . next hz =>
      exact (Nat.ne_of_lt hd.left).symm
  . induction k with
    | zero => {
      rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq]
      split
      . next hn =>
        have h1:= Nat.not_le_of_gt hd.right
        have h2:= hn.right
        contradiction
      . exact (Nat.ne_of_lt hd.left).symm
    }
    | succ k' ih =>
    rw [Nat.succ_mul, Nat.mod_eq]
    split
    . next hn =>
      rw [Nat.add_assoc, Nat.add_comm n, ← Nat.add_assoc, Nat.add_sub_cancel]
      exact ih
    . next hn =>
      have hf := not_and hn
      cases hf with
      | inl hn0 => {
        rw [Nat.not_gt_eq] at hn0
        cases hn0 with
        | refl =>
        rw [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
        exact (Nat.ne_of_lt hd.left).symm
      }
      | inr hk =>
      have hc:= Nat.le_add_left n (k'*n + d)
      rw [Nat.add_assoc, Nat.add_comm d, ← Nat.add_assoc]at hc
      contradiction

theorem succ_multiple_mod (k n d: Nat): ((succ k) * n + d) % n = (k*n+d)%n:= by
  rw [Nat.succ_mul, Nat.add_assoc, Nat.add_comm n, ← Nat.add_assoc, Nat.mod_eq_sub_mod, Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero]
  exact Nat.le_refl n
  exact Nat.le_add_left n (k*n+d)

theorem congruence (k n d: Nat)(hd: d < n): (k * n + d) % n = d := by
  induction d generalizing k with
  | zero => rw [Nat.add_zero, multiple_mod]
  | succ d' ih =>
  have hdd:= Nat.lt_of_succ_lt hd
  have ihd:= ih (succ k) hdd
  induction k with
  | zero => {
    rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq]
    split
    . next hn =>
      have h1:= Nat.not_le_of_gt hd
      have h2:= hn.right
      contradiction
    . next hn =>
      have hnn:= not_and hn
      cases hnn with
      | inl hz => rfl
      | inr hz => rfl
  }
  | succ k' hk => {
    have hf:= hk (ih (succ k') hdd)
    rw [succ_multiple_mod k' n (succ d')]
    assumption
  }

theorem le_multiple_le_succ {a n : Nat}: a ≤ k * n → a ≤ (succ k) * n:= by
  intro h
  have hk:= Nat.le_add_left (k*n) n
  rw [Nat.add_comm] at hk
  have hr:= Nat.le_trans h hk
  rw [Nat.succ_mul]
  assumption

theorem not_eq_zero {n: Nat}(hn0: n ≠ 0) : 1 ≤ n := by
  by_cases hn1: 1 ≤ n
  . assumption
  . have hn := Nat.gt_of_not_le hn1
    cases n with
    | zero => contradiction
    | succ d =>
    have h : 1 = succ zero := by trivial
    rw [h] at hn
    contradiction

theorem some_multiple_gt (a n : Nat)(hn0: n ≠ 0): ∃ k, a ≤ k * n := by
  induction a with
  | zero => exists 1; rw [Nat.one_mul]; exact Nat.zero_le n;
  | succ d hd =>
  cases hd with
  | intro k hk =>
  exists (succ k)
  rw [Nat.succ_mul, succ_eq_add_one]
  have hf := Nat.add_le_add hk (not_eq_zero hn0)
  assumption

theorem some_multiple_gt_self {a n : Nat}(ha: a ≥ n)(hn: n ≠ 0): ∃ k, a - k * n ≤ n:= by
  have hk := some_multiple_gt a n hn
  cases hk with
  | intro k hk =>
  induction a generalizing k with
  | zero => {
    exists 0
    rw [Nat.zero_mul, Nat.zero_sub]
    exact Nat.zero_le n
  }
  | succ a' _ =>
  rw [← Nat.add_zero (k*n), Nat.add_comm] at hk
  have hf:= Nat.le_trans (Nat.sub_le_of_le_add hk) (Nat.zero_le n)
  exists k

theorem mod_pattern (a n: Nat)(hn: n ≠ 0): ∃ k, (∃d, (d < n) ∧ (a = k * n + d)) := by
  by_cases h: a < n
  . exists 0, a
    rw [Nat.zero_mul, Nat.zero_add]
    constructor
    . assumption
    . rfl
  . rw [Nat.not_lt_eq] at h
    . exists (a/n), a%n
      constructor
      . apply Nat.mod_lt
        apply not_eq_zero
        assumption
      . rw [Nat.mul_comm]
        exact (Nat.div_add_mod a n).symm

theorem nat_general_pattern (a n: Nat)(hn: n ≠ 0 ): ∃k, (a = k * n + a % n) := by
  have hm:= mod_pattern a n hn
  cases hm with
  | intro k hk =>
  cases hk with
  | intro d hd =>
  have hm : a % n = (k * n + d) % n := by rw [hd.right]
  rw [congruence] at hm
  rw [hm.symm] at hd
  exists k
  exact hd.right
  exact hd.left

theorem sub_mod_mod (a n: Nat): (a - (a % n)) % n = 0 := by
  by_cases hn1: n = 1
  . rw [hn1, Nat.mod_one]
  . by_cases hn0: n = 0
    . rw [hn0, Nat.mod_zero, Nat.mod_zero, Nat.sub_self]
    . have ha:= nat_general_pattern a n hn0
      cases ha with
      | intro k hk =>
      rw [hk, congruence, Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero, multiple_mod]
      exact Nat.le_refl (a%n)
      have hn:= lt_of_succ_lt_succ (Nat.lt_succ_of_le (not_eq_zero hn0))
      exact Nat.mod_lt a hn

theorem sub_mod (a n: Nat): ∃ k, a - (a % n) = k * n := by
  by_cases hn1: n = 1
  . rw [hn1, Nat.mod_one, Nat.sub_zero]
    exists a
    rw [Nat.mul_one]
  . by_cases hn0: n = 0
    . exists 0
      rw [hn0, Nat.mod_zero, Nat.zero_mul, Nat.sub_self]
    . have ha:= nat_general_pattern a n hn0
      cases ha with
      | intro k hk =>
      exists k
      rw [hk, congruence, Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero]
      exact Nat.le_refl (a%n)
      have hn:= lt_of_succ_lt_succ (Nat.lt_succ_of_le (not_eq_zero hn0))
      exact Nat.mod_lt a hn

theorem mod_eq_zero {a : Nat}: a % n = 0 → ∃k: Nat, a = k * n:= by
  intro h
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero] at h
    rw [h, hn0]
    exists 0
  . have ha:= nat_general_pattern a n hn0
    cases ha with
    | intro k hk =>
    exists k
    rw [h, Nat.add_zero] at hk
    assumption

theorem mod_succ_pred {a n: Nat}(hn0: n ≠ 0)(han: ¬ a%n = (n-1)): a%n + 1 < n:= by
  have hn:= not_eq_zero hn0
  have ha:= Nat.mod_lt a hn
  apply Nat.add_lt_of_lt_sub
  have hs: n = succ (n-1):= by rw [succ_eq_add_one, Nat.add_comm, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left]; exact hn;
  rw (config:= {occs:= .pos [2]}) [hs] at ha
  have hp:= Nat.le_of_lt_succ ha
  exact Nat.lt_of_le_of_ne hp han

theorem mod_succ {a b n: Nat}: a % n = b % n → (succ a) % n = (succ b) % n:= by
  intro h
  by_cases hn0: n = 0
  . rw [hn0, Nat.mod_zero, Nat.mod_zero] at h
    rw [h]
  . by_cases hn1: n = 1
    . rw [hn1, Nat.mod_one, Nat.mod_one]
    . by_cases han: a%n = n - 1
      . have hbn: b%n = n - 1 := by rw [han] at h; exact h.symm
        have ha:= nat_general_pattern a n hn0
        have hb:= nat_general_pattern b n hn0
        cases ha with
        | intro ka hka =>
        cases hb with
        | intro kb hkb =>
        rw [hka, hkb, han, succ_eq_add_one, Nat.add_assoc, Nat.add_comm (n-1), ← Nat.add_sub_assoc, Nat.add_sub_cancel_left, ←Nat.succ_mul, multiple_mod ]
        rw [hbn, succ_eq_add_one, Nat.add_assoc, Nat.add_comm (n-1), ← Nat.add_sub_assoc, Nat.add_sub_cancel_left, ←Nat.succ_mul, multiple_mod ]
        exact not_eq_zero hn0
        exact not_eq_zero hn0
      . have ha:= nat_general_pattern a n hn0
        have hb:= nat_general_pattern b n hn0
        cases ha with
        | intro ka hka =>
        cases hb with
        | intro kb hkb =>
        have hbn : ¬ b%n = n - 1 := by rw [h] at han; exact han
        rw [hka, hkb, succ_eq_add_one, Nat.add_assoc, succ_eq_add_one, Nat.add_assoc, congruence, congruence, h]
        exact mod_succ_pred hn0 hbn
        exact mod_succ_pred hn0 han

theorem mod_pred {k n: Nat} (hk: k ≠ 0)(hn0: n ≠ 0): (k * n - 1) % n = (n - 1):= by
  by_cases hn1: n = 1
  . rw [hn1, Nat.sub_self, Nat.mod_one]
  . cases k with
    | zero => contradiction
    | succ d =>
    rw [Nat.succ_mul, Nat.add_sub_assoc, congruence]
    apply Nat.sub_lt
    exact Nat.zero_lt_of_ne_zero hn0
    trivial
    exact not_eq_zero hn0

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
    . by_cases han: (a%n = n - 1)
      . by_cases hbn: (b%n = n - 1)
        . rw [han, hbn]
        . have ha:= nat_general_pattern a n hn0
          have hb:= nat_general_pattern b n hn0
          cases ha with
          | intro ka hka =>
          cases hb with
          | intro kb hkb => {
            rw [succ_eq_add_one, succ_eq_add_one, hka, hkb, Nat.add_assoc, Nat.add_assoc,
             han, Nat.add_comm (n-1), ← Nat.add_sub_assoc (not_eq_zero hn0), Nat.add_sub_cancel_left,
              ←Nat.succ_mul, multiple_mod] at h
            have hc:= mod_eq_zero h.symm
            cases hc with
            | intro k hk =>
            rw [Nat.add_comm] at hk
            have hz:= Nat.sub_eq_of_eq_add hk.symm
            rw [Nat.mul_comm, Nat.mul_comm _ n,  ← Nat.mul_sub_left_distrib n] at hz
            have hcc:= Nat.sub_eq_of_eq_add hz
            have hc: (n * (k - kb) - 1) % n = (b % n) % n:= by rw [hz, Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero]; trivial;
            rw [mod_mod, Nat.mul_comm, mod_pred] at hc
            have hx:= hc.symm
            contradiction
            by_cases hk0: k - kb = 0
            . rw [hk0] at hz
              contradiction
            . assumption
            exact hn0
          }
      . by_cases hbn: (b%n = n - 1)
        . have ha:= nat_general_pattern a n hn0
          have hb:= nat_general_pattern b n hn0
          cases ha with
          | intro ka hka =>
          cases hb with
          | intro kb hkb => {
            rw [succ_eq_add_one, succ_eq_add_one, hka, hkb, Nat.add_assoc, Nat.add_assoc,
             hbn, Nat.add_comm (n-1), ← Nat.add_sub_assoc (not_eq_zero hn0), Nat.add_sub_cancel_left,
              ←Nat.succ_mul, multiple_mod] at h
            have hc:= mod_eq_zero h
            cases hc with
            | intro k hk =>
            rw [Nat.add_comm] at hk
            have hz:= Nat.sub_eq_of_eq_add hk.symm
            rw [Nat.mul_comm, Nat.mul_comm _ n,  ← Nat.mul_sub_left_distrib n] at hz
            have hcc:= Nat.sub_eq_of_eq_add hz
            have hc: (n * (k - ka) - 1) % n = (a % n) % n:= by rw [hz, Nat.add_sub_assoc, Nat.sub_self, Nat.add_zero]; trivial;
            rw [mod_mod, Nat.mul_comm, mod_pred] at hc
            have hx:= hc.symm
            contradiction
            by_cases hk0: k - ka = 0
            . rw [hk0] at hz
              contradiction
            . assumption
            exact hn0
          }
        . have ha:= nat_general_pattern a n hn0
          have hb:= nat_general_pattern b n hn0
          cases ha with
          | intro ka hka =>
          cases hb with
          | intro kb hkb =>
          rw [succ_eq_add_one, succ_eq_add_one, hka, hkb, Nat.add_assoc, Nat.add_assoc, congruence, congruence] at h
          exact Nat.add_right_cancel h
          exact mod_succ_pred hn0 hbn
          exact mod_succ_pred hn0 han

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

theorem add_in_mod (a b n: Nat): (a + b) % n = (a + b % n) % n:= by
  have hb: b%n = (b%n) %n := by exact (mod_mod b n).symm
  rw [mod_add_left_cancel b (b%n) n a] at hb
  assumption

theorem add_mod (a b n : Nat): ((a+b)%n = (a%n + b%n) %n):= by
  have ha:= add_in_mod a b n
  rw [ha, Nat.add_comm a, Nat.add_comm (a%n)]
  have hb:= add_in_mod (b%n) a n
  assumption

theorem succ_mod (a n : Nat): (succ a) % n = (succ (a % n)) % n:= by
  rw [succ_eq_add_one, succ_eq_add_one, Nat.add_comm, Nat.add_comm _ 1, add_in_mod]

theorem succ_zero_mod (a n : Nat)(hn: n ≠ 0 ∧ n ≠ 1)(h: a % n = 0): (succ a) % n = 1:= by
  rw [succ_eq_add_one, Nat.add_comm, add_in_mod, h, Nat.add_zero, one_mod hn.right]

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

theorem succ_succ_div_2 (n d: Nat): n/2 > d → (succ (succ n))/2 > succ d:= by
  intro h
  rw [succ_eq_add_one, Nat.add_assoc, one_plus_one, Nat.div_eq]
  split
  . next hn =>
    rw [Nat.add_sub_assoc , Nat.sub_self, Nat.add_zero n, ← succ_eq_add_one]
    apply Nat.succ_lt_succ
    assumption
    trivial
  . next hn =>
    have hc := not_and hn
    cases hc with
    | inl _ => contradiction
    | inr h2 =>
    have hc2:= Nat.le_add_left 2 n
    contradiction

theorem div_lt {a b n: Nat}(hn0: n ≠ 0)(ha: n < a)(hb: n < b): a < b → (a/n) < (b/n):= by
  intro h

  have han:= (Nat.div_add_mod a n).symm
  have hbn:= (Nat.div_add_mod b n).symm

  sorry
  -- rw [Nat.div_eq]
  -- split
  -- . next hna =>
  --   rw [Nat.div_eq b n]
  --   split
  --   . next hnb =>

  --     sorry
  --   . next hnb =>
  --     have hn := not_and hnb
  --     cases hn with
  --     | inl hnn0 => have hx:= Nat.zero_lt_of_ne_zero hn0; contradiction
  --     | inr hnnb => have hx:= Nat.le_of_lt hb; contradiction
  -- . next hna =>
  --   have hn := not_and hna
  --   cases hn with
  --   | inl hnn0 => have hx:= Nat.zero_lt_of_ne_zero hn0; contradiction
  --   | inr hnna => have hx:= Nat.le_of_lt ha; contradiction

theorem half_gt_3 (n: Nat)(hn: n > 7): n / 2 > 3 := by
  by_cases hn8: succ 7 = n
  . rw [hn8.symm]
    trivial
  . have hg8 := Nat.lt_of_le_of_ne (Nat.lt_of_succ_le hn) hn8
    have h8: succ 7 = 8 := by trivial
    rw [h8] at hn8 hg8
    have hs: 3 < (8/2) := by trivial
    have h8_2 : 2 < 8 := by trivial
    have h2z: 2 ≠ 0 := by trivial
    have hf:= div_lt h2z h8_2 (Nat.lt_trans h8_2 hg8) hg8
    exact Nat.lt_trans hs hf

theorem equivalent_goldbach: ∀ n: Nat, n > 3 → ∃ k: Nat, k < n ∧ prime (n - k) ∧ prime (n + k):= by
  -- this is the important insight behind the Goldbach's conjuctrue, since it corresponds to prime numbers distribution
  -- no one knows how to solve this
  intro n hn
  sorry

theorem goldbach_conjuctrue :∀ n: Nat, even n ∧ n ≥ 4 → ∃ a b: Nat, (n = a + b) ∧ (prime a) ∧ (prime b) := by
  -- no one knows how to solve this, here I'm using equivalent_goldbach to create a proof
  -- the outline of this proof is simple, try all even numbers less than 8, and use equivalent_goldbach for the rest
  intro n ⟨ hne, hn⟩
  by_cases hn4: 4 = n
  . exists 2,2
    rw [hn4.symm]
    constructor
    . trivial
    . exact And.intro prime_2 prime_2
  . by_cases hn5: 5 = n
    . have hn5o:= odd_not_even.mp odd_5
      rw [hn5.symm] at hne
      contradiction
    . by_cases hn6: 6 = n
      . exists 3, 3
        rw [hn6.symm]
        constructor
        . trivial
        . exact And.intro prime_3 prime_3
      . by_cases hn7: 7 = n
        . have hn7o:= odd_not_even.mp odd_7
          rw [hn7.symm] at hne
          contradiction
        . let d := n / 2
          have hg7: n > 7:= by exact Nat.lt_of_le_of_ne (Nat.lt_of_le_of_ne (Nat.lt_of_le_of_ne (Nat.lt_of_le_of_ne hn hn4) hn5) hn6) hn7
          have hg3:= half_gt_3 n hg7
          have hg:= equivalent_goldbach d hg3 -- this is currently an unknown task
          cases hg with
          | intro k hk=>
          have ⟨h1, hkn ⟩ := hk
          exists (d - k), (d + k)
          constructor
          . have hd:= (Nat.div_add_mod n 2).symm
            rw [Nat.add_comm, Nat.add_assoc, ← Nat.add_sub_assoc, Nat.add_sub_cancel_left
            , ← Nat.mul_one d, ← Nat.mul_add, one_plus_one, hd, hne, Nat.add_zero, Nat.mul_comm]
            exact Nat.le_of_lt h1
          . exact hkn
