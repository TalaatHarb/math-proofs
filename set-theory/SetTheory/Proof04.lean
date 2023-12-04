import SetTheory
open Set

theorem union_with_intersection_same (A B: Set α ) : A ∪ (A ∩ B) = A := by
  apply double_inclusion_left
  . intro x h
    cases h with
    | inl => assumption
    | inr hr => exact hr.left
  . intro x h
    exact Or.inl h
