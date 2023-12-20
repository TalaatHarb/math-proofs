import MyNat
import MyNat.multiplication_world

open MyNat

lemma pow_zero(a: MyNat) : a ^ zero = 1:= by
  sorry

lemma pow_succ(a b: MyNat) : a ^ succ (b) = a * (a ^ b):= by
  sorry

lemma zero_pow_zero : zero ^ zero = 1 := by
  sorry

lemma zero_pow_succ(m: MyNat) : zero ^ succ (m) = zero:= by
  sorry

lemma pow_one(a: MyNat) : a ^ 1 = a := by
  sorry

lemma pow_add(a m n: MyNat) : a ^ (m + n) = (a ^ m) * (a ^ n):= by
  sorry

lemma mul_pow(a b n: MyNat) : (a * b) ^ n = (a ^ n) * (b ^ n):= by
  sorry

lemma pow_pow(a m n: MyNat) : (a ^ m) ^ n = a ^ (m * n) := by
  sorry

lemma add_squared(a b: MyNat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b:= by
  sorry
