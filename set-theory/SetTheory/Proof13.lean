import SetTheory
open Set

theorem cross_distribute_union (A B C: Set α ) : (A × (B ∪ C)) = (A × B) ∪ (A × C):= by
  apply Set.ext
  intro p
  constructor
  . intro habc
    cases habc with
    | intro ha hbc =>
    cases hbc with
    | inl hb=>
    exact Or.inl ⟨ ha, hb ⟩
    | inr hc =>
    exact Or.inr ⟨ ha, hc ⟩
  . intro habc
    cases habc with
    | inl hab =>
    exact ⟨ hab.left, Or.inl hab.right⟩
    | inr hac =>
    exact ⟨ hac.left, Or.inr hac.right⟩
