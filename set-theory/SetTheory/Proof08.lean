import SetTheory
open Set

theorem subset_iff_intersection (A B : Set α ) : A ⊆ B ↔ A ∩ B = A  := by
  constructor
  . intro hab
    apply double_inclusion_left
    . intro x hx
      exact hx.left
    . intro x ha
      have hb : x ∈ B := by exact hab ha
      exact And.intro ha hb
  . intro h
    rw [h.symm]
    intro x haib
    exact haib.right
