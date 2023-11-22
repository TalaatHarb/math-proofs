import SetTheory
open Set

theorem diff_complement_reverse_diff (A B : Set α ) : Aᶜ \ Bᶜ = B \ A:= by
  apply Set.ext
  intro x
  constructor
  . intro hacbc
    constructor
    . have hbc := And.right hacbc
      have h:= member_set_or_complement B x
      cases h with
      | inl hb => exact hb
      | inr hbc => contradiction
    . exact hacbc.left
  . intro hba
    constructor
    . exact hba.right
    . have hb:= hba.left
      rw [<-complement_complement_set B] at hb
      exact hb
