import SetTheory
open Set

theorem empty_subset_every (A : Set α ) : ∅ ⊆ A  := by
  intro x hx
  contradiction
