import MyNat
import MyNat.addition_world

open MyNat

lemma mul_zero(a: MyNat) : a * zero = zero := by rfl

lemma mul_succ (a b : MyNat) : a * succ b = a + (a * b) := by rfl

lemma zero_mul (a: MyNat): zero * a = zero :=
  by
  induction a with
  | zero => rfl
  | succ a' ih => rewrite [mul_succ, ih] rfl

lemma mul_one (a: MyNat) : a * 1 = a :=
  by rfl

lemma one_mul (a: MyNat) : 1 * a = a :=
  by
  induction a with
  | zero => rfl
  | succ a' ih => rewrite [mul_succ, ih, add_comm, succ_eq_add_one] rfl

lemma mul_add(t a b: MyNat) : t * (a + b) = t * a + t * b :=
  by induction b with
  | zero => rfl
  | succ b' ih => rewrite [add_succ, mul_succ, mul_succ,
   ih, <- add_assoc, <- add_assoc, add_comm t] rfl

lemma mul_assoc (a b c: MyNat) : (a * b) * c = a * (b * c):=
  by induction c with
  | zero => rewrite [mul_zero, mul_zero] rfl
  | succ c' ih => rewrite [mul_succ, mul_succ, mul_add, ih] rfl

lemma succ_mul (a b: MyNat): succ (a) * b = a * b + b :=
  by induction b with
  | zero => rfl
  | succ b' ih => 
  rewrite [mul_succ, mul_succ, ih, succ_eq_add_one, succ_eq_add_one,
   <- add_assoc, <- add_assoc, add_right_comm a, add_right_comm] rfl

lemma add_mul(t a b: MyNat) : (a + b) * t = a * t + b * t :=
  by induction b with
  | zero => rewrite [add_zero, zero_mul, add_zero] rfl
  | succ b' ih => rewrite [add_succ, succ_mul, succ_mul, <- add_assoc, ih] rfl

lemma mul_comm (a b: MyNat): a * b = b * a :=
  by induction b with
  | zero => rewrite[mul_zero, zero_mul] rfl
  | succ b' ih => rewrite[succ_mul, mul_succ, ih, add_comm] rfl

lemma mul_left_comm(a b c: MyNat): (a * b) * c = b * (a * c):=
  by rewrite [mul_comm a b, mul_assoc] rfl

lemma add_same(a: MyNat) : a + a = succ (1) * a:= 
  by rewrite [succ_mul, one_mul] rfl

