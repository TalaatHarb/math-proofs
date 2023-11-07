import MyNat
import MyNat.multiplication_world
import MyNat.advanced_addition_world
import MyNat.advanced_proposition_world

open MyNat

theorem mul_pos (a b : MyNat) :
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

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : MyNat)
  (h : a * b = zero) : a = zero ∨ b = zero := by
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


theorem mul_eq_zero_iff (a b : MyNat) :
  a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  . apply eq_zero_or_eq_zero_of_mul_eq_zero
  . intro h
    exact (
      Or.elim h
      (fun ha => by rw [ha, <-zero_equal_numeral ,zero_mul])
      (fun hb => by rw [hb, <-zero_equal_numeral, mul_zero])
    )

theorem mul_left_cancel (a b c : MyNat)
  (ha : a ≠ zero) : a * b = a * c → b = c := by
  intro h
  induction c generalizing b with
    | zero =>
      rw [mul_zero] at h
      have hz:= eq_zero_or_eq_zero_of_mul_eq_zero a b h
      match hz with
        | Or.inl hz => contradiction
        | Or.inr hz => assumption
    | succ c ih =>
      cases b with
      | zero =>
        rw [mul_zero] at h
        have hz:= eq_zero_or_eq_zero_of_mul_eq_zero  a (succ c) (Eq.symm h)
        match hz with
        | Or.inl hz => contradiction
        | Or.inr hz => exact Eq.symm hz
      | succ b =>
        rw [mul_succ, mul_succ] at h
        have hf := ih b (add_left_cancel (a*b) (a*c) a h)
        rw [hf]
