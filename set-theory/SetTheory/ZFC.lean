-- Define the type of sets
axiom Set : Type

-- Define the membership relation
axiom ElementOf : Set → Set → Prop
infix:50 " ∈ " => ElementOf

-- Define the empty set
axiom empty : Set

-- Define the axiom of extensionality
axiom extensionality : ∀ {a b : Set}, (∀ x, x ∈ a ↔ x ∈ b) → a = b

-- Define the axiom of regularity
axiom regularity : ∀ a : Set, a ≠ empty → ∃ b : Set, b ∈ a ∧ ∀ x, x ∈ b → ¬(x ∈ a)

-- Define the axiom of pairing
axiom pairing : ∀ a b : Set, ∃ c : Set, ∀ x, x ∈ c ↔ (x = a ∨ x = b)

-- Define the axiom of union
axiom union : ∀ a : Set, ∃ b : Set, ∀ x, x ∈ b ↔ ∃ y, y ∈ a ∧ x ∈ y

-- Define the axiom of power set
axiom power_set : ∀ a : Set, ∃ b : Set, ∀ x, x ∈ b ↔ ∀ y, y ∈ x → y ∈ a

-- Define the axiom of choice
axiom choice : ∀ {a : Set → Prop}, (∀ x, ∃ y, a x → y ∈ x) → ∃ f : Set → Set, ∀ x, a x → f x ∈ x