import MyNat
open MyNat

def le(a b: MyNat ) := ∃ (c: MyNat ), b = a + c

instance : LE MyNat where
  le := le

theorem le_iff_exists_add (a b : MyNat) :
  a ≤ b ↔ ∃ (c : MyNat), b = a + c :=
  Iff.rfl

def lt (a b : ℕ) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT MyNat where
  lt := lt
