import SetTheory
open Set

theorem subset_of_complement (A B: Set α ) (h: A ∩ B = ∅ ) : A ⊆ Bᶜ := by
  intro x ha hb
  have hc: x ∈ Set.inter A B := by exact (And.intro ha hb)
  have hr:= element_member_int_not_empty hc
  contradiction
