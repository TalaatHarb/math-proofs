import MyNat
import MyNat.lemma

open MyNat

/-Tutorial world -/
lemma rfl_example (x y z : MyNat) : x*y+z = x*y+z := by
  sorry

lemma rewrite_example (x y: MyNat) (h: y =x+7) : 2 * y = 2 * (x + 7) := by
  sorry

lemma rewrite_example_2 (a b: MyNat) (h: succ (a) = b) : succ (succ (a)) = succ (b) := by
  sorry

lemma add_zero (a: MyNat) : a + zero = a := by
  sorry

lemma add_succ (a d: MyNat) : a + succ (d) = succ (a + d) := by
  sorry

lemma add_succ_zero (a: MyNat) : a + succ (zero) = succ (a) := by
  sorry
