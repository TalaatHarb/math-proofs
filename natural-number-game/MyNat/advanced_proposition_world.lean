import MyNat
import MyNat.proposition_world

open MyNat

lemma and_prop(P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  sorry

lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry

lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

example (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  sorry

example (P Q : Prop) : Q → (P ∨ Q) := by
  sorry

lemma or_symm (P Q : Prop) : P ∨ Q -> Q ∨ P := by
  sorry

lemma and_or_distrib_left (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  sorry

lemma and_or_common_factor (P Q R : Prop) : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  sorry

lemma and_or_distrib_left_iff (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q := by
  sorry

lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  sorry

lemma full_contrapositive (P Q : Prop) : (¬ Q → ¬ P) ↔ (P → Q) := by
  sorry

lemma not_and (P Q : Prop) : ¬(P ∧ Q) → (¬P) ∨ (¬Q) := by
  sorry

lemma not_or (P Q : Prop) : ¬(P ∨ Q) → (¬P) ∧ (¬Q) := by
  sorry

lemma not_and_not (P Q: Prop): ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  sorry

lemma not_or_not (P Q: Prop): ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry

lemma not_and_iff (P Q : Prop) : (¬P) ∨ (¬Q) ↔ ¬ (P ∧ Q) := by
  sorry

lemma not_or_iff (P Q : Prop) : (¬P) ∧ (¬Q) ↔ ¬ (P ∨ Q) := by
  sorry
