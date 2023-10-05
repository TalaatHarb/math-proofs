import SetTheory
open Set

theorem set_inter_union_is_subset (A B: Set α ) : A ∩ (A ∪ B) ⊆ A := by
  intro x h
  exact h.left

theorem elem_in_set_is_in_union (A B: Set α ) (h: x ∈ A) : x ∈ (A ∪ B) := by
  apply Or.inl
  exact h

theorem inter_union_is_subset (A B: Set α ) : A ⊆ A ∩ (A ∪ B) := by
  intro x h
  apply And.intro
  exact h
  exact elem_in_set_is_in_union A B h

theorem set_inter_union_is_same (A B: Set α ) : A ∩ (A ∪ B) = A := by
  apply subset_iff_is_equal
  apply set_inter_union_is_subset
  apply inter_union_is_subset