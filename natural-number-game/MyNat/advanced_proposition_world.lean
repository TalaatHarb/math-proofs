import MyNat
import MyNat.proposition_world

open MyNat

lemma and_prop(P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  . exact p
  . exact q

lemma and_symm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro hpq
  cases hpq with
  | intro hp hq =>
    constructor
    . exact hq
    . exact hp

lemma and_trans (P Q R : Prop) : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hpq hqr
  cases hpq with
  | intro hp hq =>
    cases hqr with
    | intro hq hr =>
      constructor
      . exact hp
      . exact hr

lemma iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq2 hqr2
  cases hpq2 with
  | intro hpq hqp =>
  cases hqr2 with
  | intro hqr hrq =>
    constructor
    . intro hp
      exact hqr (hpq hp)
    . intro hr
      exact hqp (hrq hr)

example (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq2 hqr2
  constructor
  . intro hp
    apply Iff.mp hqr2
    apply Iff.mp hpq2
    exact hp
  . intro hr
    rewrite [hpq2, hqr2]
    exact hr


example (P Q : Prop) : Q → (P ∨ Q) := by
  intro hq
  exact Or.inr hq

lemma or_symm (P Q : Prop) : P ∨ Q -> Q ∨ P := by
  intro hpq
  exact Or.elim hpq Or.inr Or.inl

lemma and_or_distrib_left (P Q R : Prop) :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro hpAqr
  let hp := hpAqr.left
  let hqr := hpAqr.right
  exact (
    Or.elim hqr
    (fun hq => Or.inl (And.intro hp hq))
    (fun hr => Or.inr (And.intro hp hr))
  )

lemma and_or_common_factor (P Q R : Prop) :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  intro hpAqOpAr
  exact (
    Or.elim hpAqOpAr
    (fun hpAq =>
      let hp := hpAq.left
      let hq := hpAq.right
      And.intro hp (Or.inl hq)
    )
    (fun hpAr =>
      let hp := hpAr.left
      let hr := hpAr.right
      And.intro hp (Or.inr hr)
    )
  )

lemma and_or_distrib_left_iff (P Q R : Prop) :
  P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  . apply and_or_distrib_left
  . apply and_or_common_factor

lemma contra (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro hpAnp
  let hp := hpAnp.left
  let hnp := hpAnp.right
  exact False.elim (hnp hp)

lemma contrapositive2 (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := by
  intro hnqnp hp
  by_cases hq : Q
  . case inl => exact hq
  . case inr => exact absurd hp (hnqnp hq)


lemma full_contrapositive (P Q : Prop) : (¬ Q → ¬ P) ↔ (P → Q) := by
  constructor
  . apply contrapositive2
  . apply contrapositive

lemma not_and (P Q : Prop) : ¬(P ∧ Q) → (¬P) ∨ (¬Q) := by
  intro h
  by_cases hp : P
  . by_cases hq : Q
    . have hpq := And.intro hp hq
      contradiction
    . exact Or.inr hq
  . by_cases hq : Q
    . exact Or.inl hp
    . exact Or.inl hp

lemma not_or (P Q : Prop) : ¬(P ∨ Q) → (¬P) ∧ (¬Q) := by
  intro hnpq
  constructor
  . intro hp
    have hpq := Or.intro_left Q hp
    contradiction
  . intro hq
    have hpq := Or.intro_right P hq
    contradiction

lemma not_and_not (P Q: Prop): ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro hnpnq hpq
  cases hnpnq with
  | intro hnp hnq =>
  cases hpq
  . contradiction
  . contradiction

lemma not_or_not (P Q: Prop): ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  intro hnpq hpq
  have hp := hpq.left
  have hq := hpq.right
  cases hnpq
  . contradiction
  . contradiction

lemma not_and_iff (P Q : Prop) : (¬P) ∨ (¬Q) ↔ ¬ (P ∧ Q) := by
  constructor
  . exact not_or_not P Q
  . exact not_and P Q


lemma not_or_iff (P Q : Prop) : (¬P) ∧ (¬Q) ↔ ¬ (P ∨ Q) := by
  constructor
  . exact not_and_not P Q
  . exact not_or P Q
