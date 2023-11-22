import SetTheory
open Set

theorem cross_subset_trans (A B : Set α )(C D: Set β) (hab: A ⊆ B)(hcd: C ⊆ D) : (A × C) ⊆ (B × D) := by
  intro xy hxy
  cases hxy with
  | intro hx hy=>
  have hxb : xy.fst ∈ B := by exact hab hx
  have hyd : xy.snd ∈ D := by exact hcd hy
  exact ⟨ hxb, hyd⟩
