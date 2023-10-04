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

infix:70 " ∩ " => inter
infixl:65 " ∪ " => union
infix:50 " ⊆ " => subset

theorem subset_iff_is_equal (A B: Set α ) (h1: A ⊆ B) (h2: B ⊆ A) : A = B := by
  
  sorry