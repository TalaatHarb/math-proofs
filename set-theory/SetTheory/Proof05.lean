import SetTheory
open Set

theorem union_inter_complement_is_diff (A B: Set α ) : (A ∪ B) ∩ Aᶜ = B \ A := by
  apply double_inclusion
  . intro x h
    constructor
    . have hu: x ∈ A ∪ B := by exact h.left
      have hc: ¬ x ∈ A := by exact h.right
      cases hu with
      | inl => contradiction
      | inr => assumption
    . exact h.right
  . intro x h
    constructor
    . exact Or.inr (h.left)
    . exact h.right
