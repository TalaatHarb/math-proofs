import MyNat
import MyNat.addition_world

open MyNat

lemma succ_inj (a b: ℕ ): succ a = succ b → a = b := by
  intro hsasb
  cases hsasb
  rfl

lemma zero_ne_succ (a: ℕ ) : zero ≠ succ a := by
  intro hz
  cases hz

lemma succ_succ_inj (a b: ℕ ) : succ (succ a) = succ (succ b) → a = b := by
  intro hab
  cases hab
  rfl

lemma succ_eq_succ_of_eq (a b : ℕ ) : a = b → succ a = succ b := by
  intro hab
  rewrite [hab] rfl

lemma succ_eq_succ_iff (a b : ℕ ): a = b ↔ succ a = succ b := by
  constructor
  apply succ_eq_succ_of_eq
  apply succ_inj

theorem add_right_cancel (a b t: ℕ ): a + t = b + t → a = b := by
  intro hatb
  induction t with
  | zero => 
    rewrite [add_zero , add_zero] at hatb
    exact hatb
  | succ t' ih =>
    rewrite [add_succ, add_succ] at hatb
    let h := (succ_inj (a + t') (b + t') hatb)
    apply ih h
    
theorem add_left_cancel (a b t: ℕ ): t + a = t + b → a = b := by
  rewrite [add_comm, add_comm t b]
  apply add_right_cancel

theorem add_right_cancel_iff (a b t: ℕ ): a + t = b + t ↔ a = b := by
  constructor
  apply add_right_cancel
  intro hab
  rewrite [hab]
  rfl

lemma eq_zero_of_add_right_eq_self (a b : ℕ) :
  a + b = a → b = 0 := by
  rewrite [<- add_zero a]
  apply add_left_cancel

theorem succ_ne_zero (a : ℕ) : succ a ≠ 0 := by
  intro hsa
  exact zero_ne_succ a hsa.symm


lemma add_left_eq_zero 
  (a b : ℕ) (H : a + b = 0) : b = 0 := by
  induction a with
  | zero => 
    rewrite [zero_add] at H
    exact H
  | succ a' _ =>
    rewrite [succ_add] at H
    let h' := succ_ne_zero (a'+ b) H
    exact False.elim h'

lemma add_right_eq_zero (a b : ℕ) : 
  a + b = 0 → a = 0 := by
  rewrite [add_comm]
  apply add_left_eq_zero

lemma add_one_eq_succ (d : ℕ) : d + 1 = succ d := by
  apply succ_eq_add_one

lemma ne_succ_self (n : ℕ) : n ≠ succ n := by
  rewrite [succ_eq_add_one, <-add_zero n, add_assoc, zero_add]
  intro h
  let h' := add_left_cancel _ _ _ h
  rewrite [one_eq_succ_zero] at h'
  exact zero_ne_succ _ h' 
  
    

