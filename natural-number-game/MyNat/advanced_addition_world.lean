import MyNat
import MyNat.addition_world

open MyNat

lemma succ_inj (a b: MyNat ): succ a = succ b → a = b := by
  intro hsasb
  cases hsasb
  rfl

lemma zero_ne_succ (a: MyNat ) : zero ≠ succ a := by
  intro hz
  cases hz

lemma succ_succ_inj (a b: MyNat ) : succ (succ a) = succ (succ b) → a = b := by
  intro hab
  cases hab
  rfl

lemma succ_eq_succ_of_eq (a b : MyNat ) : a = b → succ a = succ b := by
  intro hab
  rw [hab]

lemma succ_eq_succ_iff (a b : MyNat ): a = b ↔ succ a = succ b := by
  constructor
  . apply succ_eq_succ_of_eq
  . apply succ_inj

theorem add_right_cancel (a b t: MyNat ): a + t = b + t → a = b := by
  intro hatb
  induction t with
  | zero =>
    rw [add_zero , add_zero] at hatb
    exact hatb
  | succ t' ih =>
    rw [add_succ, add_succ] at hatb
    let h := (succ_inj (a + t') (b + t') hatb)
    apply ih h

theorem add_left_cancel (a b t: MyNat ): t + a = t + b → a = b := by
  rw [add_comm, add_comm t b]
  apply add_right_cancel

theorem add_right_cancel_iff (a b t: MyNat ): a + t = b + t ↔ a = b := by
  constructor
  . apply add_right_cancel
  . intro hab
    rw [hab]

lemma eq_zero_of_add_right_eq_self (a b : MyNat) :
  a + b = a → b = 0 := by
  rw [<- add_zero a]
  apply add_left_cancel

theorem succ_ne_zero (a : MyNat) : succ a ≠ 0 := by
  intro hsa
  exact zero_ne_succ a hsa.symm


lemma add_left_eq_zero
  (a b : MyNat) (H : a + b = zero) : b = zero := by
  induction a with
  | zero =>
    rw [zero_add] at H
    exact H
  | succ a' _ =>
    rw [succ_add] at H
    let h' := succ_ne_zero (a'+ b) H
    exact False.elim h'

lemma add_right_eq_zero (a b : MyNat) :
  a + b = zero → a = zero := by
  rw [add_comm]
  apply add_left_eq_zero

lemma add_one_eq_succ (d : MyNat) : d + 1 = succ d := by
  apply succ_eq_add_one

lemma ne_succ_self (n : MyNat) : n ≠ succ n := by
  rw [succ_eq_add_one, <-add_zero n, add_assoc, zero_add]
  intro h
  let h' := add_left_cancel _ _ _ h
  rw [one_eq_succ_zero] at h'
  exact zero_ne_succ _ h'
