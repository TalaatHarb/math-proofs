namespace Set
universe u
def Set (α : Type u) := α → Prop

def mem (x : α) (a : Set α) := a x

infix:50 (priority := high) " ∈ " => mem

def empty : Set α := fun _ => False

notation (priority := high) " ∅ " => empty

def inter (A B : Set α) : Set α :=
  fun x => x ∈ A ∧ x ∈ B

def union (A B : Set α) : Set α :=
  fun x => x ∈ A ∨ x ∈ B

def subset (A B : Set α) : Prop :=
  ∀ {x}, x ∈ A → x ∈ B

def complement(A: Set α) : Set α :=
  fun x => ¬ (x ∈ A)

def difference(A B: Set α ): Set α :=
  fun x => x ∈ A ∧ (¬ x ∈ B)

infix:70 " ∩ " => inter
infixl:65 " ∪ " => union
infix:50 " ⊆ " => subset
postfix:100 "ᶜ " => complement
infix:75 " \\ " => difference
infix:80 " - " => difference

axiom ext (α : Type _) (A B : Set α) : (∀ x, x ∈ A ↔ x ∈ B) → A = B

end Set

open Set

theorem double_inclusion {A B: Set α } : A ⊆ B ∧ B ⊆ A ↔ A = B := by
  constructor
  . intro h
    have h1 : A ⊆ B := by exact h.left
    have h2 : B ⊆ A := by exact h.right
    apply ext
    rw [subset] at h1
    rw [subset] at h2
    intro x
    apply Iff.intro
    apply h1
    apply h2
  . intro h
    constructor
    . intro x ha
      have hb: x ∈ B := by rw [h] at ha; assumption
      exact hb
    . intro x hb
      have ha: x ∈ A := by rw [h.symm] at hb; assumption
      exact ha

theorem double_inclusion_left {A B: Set α } (h1: A ⊆ B) (h2: B ⊆ A) : A = B := by
  exact double_inclusion.mp (And.intro h1 h2)

theorem double_inclusion_right {A B: Set α } (h: A = B) : A ⊆ B ∧ B ⊆ A := by
  exact double_inclusion.mpr h

theorem element_member_int_not_empty {A B: Set α } {x: α} (h: x ∈ A ∩ B): A ∩ B ≠ ∅ := by
  intro hc
  rw [hc] at h
  contradiction
