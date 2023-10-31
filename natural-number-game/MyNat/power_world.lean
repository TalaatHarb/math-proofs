import MyNat
import MyNat.multiplication_world

open MyNat

lemma pow_zero(a: MyNat) : a ^ zero = 1:= rfl
lemma pow_succ(a b: MyNat) : a ^ succ (b) = a * (a ^ b):= rfl
lemma zero_pow_zero : zero ^ zero = 1 := rfl
lemma zero_pow_succ(m: MyNat) : zero ^ succ (m) = zero:=
  by induction m with
  | zero => rfl
  | succ m' => rw [pow_succ, zero_mul]

lemma pow_one(a: MyNat) : a ^ 1 = a := rfl

lemma pow_add(a m n: MyNat) : a ^ (m + n) = (a ^ m) * (a ^ n):=
  by induction n with
  | zero => rw[add_zero, pow_zero, mul_one]
  | succ n' ih => rw[pow_succ, add_succ, pow_succ, ih,
   <- mul_assoc, <- mul_assoc, mul_comm a]

lemma mul_pow(a b n: MyNat) : (a * b) ^ n = (a ^ n) * (b ^ n):=
  by induction n with
  | zero => rw[pow_zero, pow_zero, pow_zero, mul_one]
  | succ n' ih => rw [pow_succ, ih, pow_succ, pow_succ, mul_assoc, mul_assoc,
   <-mul_left_comm, <-mul_left_comm b, <-mul_assoc,
   <-mul_assoc, <-mul_assoc, mul_comm a]

lemma pow_pow(a m n: MyNat) : (a ^ m) ^ n = a ^ (m * n) :=
  by induction n with
  | zero => rfl
  | succ n' ih => rw [pow_succ, mul_succ, pow_add, ih]

lemma add_squared(a b: MyNat) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b:=
  by rw [two_eq_succ_one, pow_succ, pow_one, pow_succ, pow_one, pow_succ, pow_one,
  mul_add, add_mul, add_mul, mul_comm b a, add_comm (a*a), add_right_comm, <-add_assoc,
  add_same, add_comm, add_comm (succ 1 * (a*b)), <-add_assoc, mul_assoc]
