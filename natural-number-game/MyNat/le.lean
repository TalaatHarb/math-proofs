import MyNat
open MyNat

def le(a b: MyNat ) := ∃ (c: MyNat ), b = a + c

instance : LE MyNat where
  le := le

theorem le_iff_exists_add (a b : MyNat) : a ≤ b ↔ ∃ (c : MyNat), b = a + c := by
  sorry

def lt (a b : MyNat) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT MyNat where
  lt := lt

theorem lt_def (a b: MyNat):  a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := by
  sorry
