import MyNat
import MyNat.addition_world

open MyNat

lemma mul_zero(a: MyNat) : a * zero = zero := by rfl

lemma mul_succ (a b : MyNat) : a * succ b = a + (a * b) := by rfl

lemma zero_mul (a: MyNat): zero * a = zero :=
  by
  induction a with
  | zero => rfl
  | succ a' ih => rw [mul_succ, ih, zero_add]

lemma mul_one (a: MyNat) : a * 1 = a :=
  by rfl

lemma one_mul (a: MyNat) : 1 * a = a :=
  by
  induction a with
  | zero => rfl
  | succ a' ih => rw [mul_succ, ih, add_comm, succ_eq_add_one]

lemma mul_add(t a b: MyNat) : t * (a + b) = t * a + t * b :=
  by induction b with
  | zero => rfl
  | succ b' ih => rw [add_succ, mul_succ, mul_succ,
   ih, <- add_assoc, <- add_assoc, add_comm t]

lemma mul_assoc (a b c: MyNat) : (a * b) * c = a * (b * c):=
  by induction c with
  | zero => rw [mul_zero, mul_zero, mul_zero]
  | succ c' ih => rw [mul_succ, mul_succ, mul_add, ih]

lemma succ_mul (a b: MyNat): succ (a) * b = a * b + b :=
  by induction b with
  | zero => rfl
  | succ b' ih =>
    rw [mul_succ, mul_succ, ih, succ_eq_add_one, succ_eq_add_one,
   <- add_assoc, <- add_assoc, add_right_comm a, add_right_comm]

lemma add_mul(t a b: MyNat) : (a + b) * t = a * t + b * t :=
  by induction b with
  | zero => rw [add_zero, zero_mul, add_zero]
  | succ b' ih => rw [add_succ, succ_mul, succ_mul, <- add_assoc, ih]

lemma mul_comm (a b: MyNat): a * b = b * a :=
  by induction b with
  | zero => rw[mul_zero, zero_mul]
  | succ b' ih => rw[succ_mul, mul_succ, ih, add_comm]

lemma mul_left_comm(a b c: MyNat): (a * b) * c = b * (a * c):=
  by rw [mul_comm a b, mul_assoc]

lemma add_same(a: MyNat) : a + a = succ (1) * a:=
  by rw [succ_mul, one_mul]
