import SetTheory

theorem set_inter_union_is_subset (A B: Set α ) : A ∩ (A ∪ B) ⊆ A := by
  intro x h
  exact h.left

theorem inter_union_is_subset (A B: Set α ) : A ⊆ A ∩ (A ∪ B) := by
  intro x h
  sorry


theorem set_inter_union_is_same (A B: Set α ) : A ∩ (A ∪ B) = A := by
  
  sorry