import SetTheory
open Set

theorem diff_is_inter_complement (A B: Set α ) : B \ A = B ∩ Aᶜ := by
  apply Set.ext
  intro x
  constructor
  . intro ha
    constructor
    . exact ha.left
    . exact ha.right
  . intro hbc
    constructor
    . exact hbc.left
    . exact hbc.right
