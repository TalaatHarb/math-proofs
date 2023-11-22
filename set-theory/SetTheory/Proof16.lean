import SetTheory
open Set

theorem union_complement_is_inter_of_complements (A B: Set α ) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply Set.ext
  intro x
  constructor
  . intro h
    constructor
    . intro ha
      have hu : x ∈ A ∪ B := by exact Or.inl ha
      contradiction
    . intro hb
      have hu : x ∈ A ∪ B := by exact Or.inr hb
      contradiction
  . intro h hx
    have hac:= h.left
    have hbc:= h.right
    cases hx with
    | inl ha => contradiction
    | inr hb => contradiction
