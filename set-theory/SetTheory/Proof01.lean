import SetTheory
open Set

theorem inter_element_part_of_left_set (A B: Set α) (h: x ∈ A ∩ B) : x ∈ A := by
  exact h.left

theorem inter_element_part_of_right_set (A B: Set α) (h: x ∈ A ∩ B) : x ∈ B := by
  exact h.right

theorem inter_element_part_of_union (A B: Set α) (h: x ∈ A ∩ B) : x ∈ A ∪ B := by
  exact Or.inl h.left

theorem inter_subset_left (A B : Set α) : A ∩ B ⊆ A := by
  intro x
  exact inter_element_part_of_left_set A B

theorem inter_subset_right (A B : Set α) : A ∩ B ⊆ B := by
  intro x
  exact inter_element_part_of_right_set A B

theorem inter_subset_union (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  intro x
  exact inter_element_part_of_union A B