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

def complement (A: Set α): Set α :=
  fun x => ¬ (x ∈ A)

def difference(A B: Set α): Set α :=
  fun x => x ∈ A ∧ (¬ x ∈ B)

def cross(A : Set α)(B: Set β): Set (α × β):=
  fun p: α × β  => p.fst ∈ A ∧ p.snd ∈ B

def powerSet {α : Type} (s : Set α) : Set (Set α) :=
  fun x => (subset x s )

infix:70 " ∩ " => inter
infixl:65 " ∪ " => union
infix:50 " ⊆ " => subset
postfix:100 "ᶜ " => complement
infix:75 " - " => difference
infix:80 " \\ " => difference
infix:30 (priority := high) " × " => cross
notation "𝒫 " => powerSet

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

theorem member_set_or_complement (A : Set α ) (x: α) : x ∈ A ∨ x ∈ Aᶜ := by
  by_cases h: x ∈ A
  . exact Or.inl h
  . exact Or.inr h

theorem not_set_iff_complement (A: Set α) (x: α ) : ¬ x ∈ A ↔ x ∈ Aᶜ:= by
  constructor
  . intro hna
    exact hna
  . intro hac
    exact hac

theorem complement_complement_set(A: Set α ) : (Aᶜ)ᶜ = A := by
  apply Set.ext
  intro x
  constructor
  . intro hacc
    by_cases ha: x ∈ A
    . exact ha
    . have hc: x ∈ Aᶜ := by exact ha
      contradiction
  . intro ha
    by_cases hc: x ∈ Aᶜ
    . contradiction
    . exact hc
