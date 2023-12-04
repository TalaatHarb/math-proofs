import SetTheory

open Set

theorem subset_trans {A B C: Set α }: A ⊆ B ∧ B ⊆ C → A ⊆ C := by
  intro ⟨ hab, hbc⟩
  intro x hx
  have hxb := hab hx
  exact hbc hxb

theorem subset_self (A : Set α): A ⊆ A := by
  intro _ hx
  apply hx

theorem subset_imp_powrset_subset {A B: Set α} : A ⊆ B → powerSet A ⊆ powerSet B:= by
  intro h x hx
  have ha: x ⊆ A := by exact hx
  have hb: x ⊆ B := by exact subset_trans ⟨ ha, h⟩
  apply hb

theorem equal_sets_equal_powersets (A B: Set α) : A = B → powerSet A = powerSet B:= by
  intro h
  have ⟨h1, h2⟩ := double_inclusion_right h
  exact double_inclusion.mp ⟨ subset_imp_powrset_subset h1, subset_imp_powrset_subset h2 ⟩

theorem powerset_subset_set_subset {A B: Set α }: (powerSet A) ⊆ (powerSet B) → A ⊆ B := by
  intro h
  have ha: A ⊆ A := by exact subset_self A
  have ha': A ∈ powerSet A := by exact ha
  have hb': A ∈ powerSet B := by exact h ha'
  have hb : A ⊆ B := by exact hb'
  apply hb

theorem subset_iff_powerset_subset{A B: Set α }: A ⊆ B ↔ powerSet A ⊆ powerSet B := by
  constructor
  . exact subset_imp_powrset_subset
  . exact powerset_subset_set_subset

theorem equal_powersets_equal_sets (A B: Set α) : powerSet A = powerSet B → A = B := by
  intro h
  have ⟨h1, h2⟩ := double_inclusion_right h
  have hab: A ⊆ B := by exact powerset_subset_set_subset h1
  have hba: B ⊆ A := by exact powerset_subset_set_subset h2
  exact double_inclusion_left hab hba

theorem equal_sets_iff_equal_powersets (A B: Set α ): A = B ↔ powerSet A = powerSet B:= by
  constructor
  . exact equal_sets_equal_powersets A B
  . exact equal_powersets_equal_sets A B
