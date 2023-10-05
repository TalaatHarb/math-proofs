namespace Set
def Set (α : Type _) := α → Prop

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

infix:70 " ∩ " => inter
infixl:65 " ∪ " => union
infix:50 " ⊆ " => subset

axiom ext (α : Type _) (A B : Set α) : (∀ x, x ∈ A ↔ x ∈ B) → A = B

end Set

open Set

theorem subset_iff_is_equal (A B: Set α ) (h1: A ⊆ B) (h2: B ⊆ A) : A = B := by
  apply ext 
  rw [subset] at h1
  rw [subset] at h2
  intro x
  apply Iff.intro
  apply h1
  apply h2