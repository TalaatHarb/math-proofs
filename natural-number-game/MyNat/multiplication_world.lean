import MyNat
import MyNat.addition_world

open MyNat

lemma mul_zero(a: MyNat) : a * zero = zero := by
  sorry

lemma mul_succ (a b : MyNat) : a * succ b = a + (a * b) := by
  sorry

lemma zero_mul (a: MyNat): zero * a = zero := by
  sorry

lemma mul_one (a: MyNat) : a * 1 = a := by
  sorry

lemma one_mul (a: MyNat) : 1 * a = a := by
  sorry

lemma mul_add(t a b: MyNat) : t * (a + b) = t * a + t * b := by
  sorry

lemma mul_assoc (a b c: MyNat) : (a * b) * c = a * (b * c):= by
  sorry

lemma succ_mul (a b: MyNat): succ (a) * b = a * b + b := by
  sorry

lemma add_mul(t a b: MyNat) : (a + b) * t = a * t + b * t := by
  sorry

lemma mul_comm (a b: MyNat): a * b = b * a := by
  sorry

lemma mul_left_comm(a b c: MyNat): (a * b) * c = b * (a * c):= by
  sorry

lemma add_same(a: MyNat) : a + a = succ (1) * a:= by
  sorry
