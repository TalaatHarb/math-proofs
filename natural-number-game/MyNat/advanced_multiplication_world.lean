import MyNat
import MyNat.multiplication_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

open MyNat

theorem mul_pos (a b : ℕ) :
  a ≠ zero → b ≠ zero → a * b ≠ zero := by
  intro ha hb
  induction a with
  | zero =>
    exact False.elim ha.irrefl
  | succ a' _ =>
    induction b with
    | zero => exact False.elim hb.irrefl
    | succ b' _ =>
      rw [succ_mul, add_succ]
      apply succ_ne_zero

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : ℕ)
  (h : a * b = 0) : a = 0 ∨ b = 0 := by
  induction a with
  | zero =>
    apply Or.inl
    rfl
  | succ a' _ =>
    apply Or.inr
    rw [succ_mul] at h
    induction b with
    | zero =>
      rfl
    | succ b' _ =>
      rw [add_succ] at h
      contradiction


theorem mul_eq_zero_iff (a b : ℕ) :
  a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  {
  apply eq_zero_or_eq_zero_of_mul_eq_zero
  }
  {
  intro h
  exact (
    Or.elim h
    (fun ha => by
    rw [ha, <-zero_equal_numeral ,zero_mul]
    )
    (fun hb => by
    rw [hb, <-zero_equal_numeral, mul_zero]
    )
    )
  }

theorem mul_left_cancel (a b c : ℕ)
  (ha : a ≠ 0) : a * b = a * c → b = c := by
  intro habc
  induction c generalizing b with
  | zero =>
    rw [mul_zero] at habc
    let h := eq_zero_or_eq_zero_of_mul_eq_zero _ _ habc
    exact(
      Or.elim h
      (fun a0 => False.elim (ha a0))
      id
    )
  | succ c' ih =>
    induction b with
    | zero =>
      rw [mul_zero] at habc
      let h := eq_zero_or_eq_zero_of_mul_eq_zero _ _ habc.symm
      exact(
        Or.elim h
        (fun a0 => False.elim (ha a0))
        (fun c0 => False.elim (succ_ne_zero _ c0))
      )
    | succ b' _ =>
      rw [mul_succ, mul_succ] at habc
      let h := add_left_cancel _ _ _ habc
      let h' := (ih b') h
      rw [h']
