import SetTheory
open Set

theorem inter_distribute_union (A B C: Set α ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C):= by
  apply Set.ext
  intro x
  constructor
  . intro habc
    have ha:= habc.left
    have hbc:= habc.right
    cases hbc with
    | inl hb => exact Or.inl (And.intro ha hb)
    | inr hc => exact Or.inr (And.intro ha hc)
  . intro habc
    constructor
    . cases habc with
      | inl hab => exact hab.left
      | inr hac => exact hac.left
    . cases habc with
      | inl hab => exact Or.inl hab.right
      | inr hac => exact Or.inr hac.right
