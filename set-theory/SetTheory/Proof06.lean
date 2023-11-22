import SetTheory
open Set

theorem inter_complement_is_union_of_complements (A B: Set α ) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  apply Set.ext
  intro x
  constructor
  . intro h
    by_cases ha: x ∈ A
    . by_cases hb: x ∈ B
      . have hi:= And.intro ha hb
        contradiction
      . exact Or.inr hb
    . exact Or.inl ha
  . intro h
    cases h with
    | inl hac=>
    intro hi
    have ha := And.left hi
    contradiction
    | inr hbc =>
    intro hi
    have hb := And.right hi
    contradiction
