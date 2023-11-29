import Collatz

open collatz

theorem coll10 : collatz 10 := by
apply coll_even 5
apply coll_odd 2
apply coll_even 8
apply coll_even 4
apply coll_even 2
apply coll_even 1
apply coll1

-- if m is odd then 3m+1 is always even, so we can go from m=2n+1 to 6n+4 and then to 3n+2 in one step.
theorem coll_odd' (n : Nat) : collatz (3 * n + 2) → collatz (2 * n + 1) := by
  intro h
  apply coll_odd
  have he: 6*n+4 = 2 *(3*n+2) := by simp [Nat.mul_add, <-Nat.mul_assoc]
  rw [he]
  apply coll_even
  assumption

theorem coll_power_of_2_decent (n: Nat): collatz (2 ^ n) → collatz (2 ^ (n+1)):= by
  rw [Nat.pow_succ, Nat.mul_comm]
  apply coll_even

theorem coll_power_of_2 (n: Nat): collatz (2 ^ n) := by
  induction n with
  | zero => exact coll1
  | succ n' ih =>
  rw [Nat.succ_eq_add_one]
  exact coll_power_of_2_decent n' ih

-- now we can go a bit quicker
theorem coll10' : collatz 10 := by
  apply coll_even 5
  apply coll_odd' 2
  apply coll_even 4
  have h: 4 = 2 ^ 2 := by simp
  rw [h]
  exact coll_power_of_2 2

theorem coll256 : collatz 256 := by
  have h: 256 = 2 ^ 8 := by simp
  rw [h]
  exact coll_power_of_2 8

-- Of course one should really be using a home-grown tactic to figure out which
-- of coll_even, coll_odd and coll1 to apply next.

/- this is the Collatz conjecture -/
theorem collatz_conjecture : ∀ n : Nat, collatz n := by
  sorry
-- Nobody knows how to prove this.
