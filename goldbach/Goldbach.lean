def divides (m n : Nat) : Prop := n % m = 0

infix:50 (priority := high) " | "  divides

def even (n : Nat) : Prop := 2 | n
def odd (n: Nat) : Prop := ¬ (2 | n)

def prime (m: Nat) : Prop :=
  m ≥ 2 ∧ ∀ (n : Nat), 1 < n ∧ n < m → ¬ n | m
