/-- collatz n means the collatz conjecture is true for n -/
inductive collatz : Nat → Prop
| coll0 : collatz 0
| coll1 : collatz 1
| coll_even : ∀ n : Nat, collatz n → collatz (2 * n)
| coll_odd : ∀ n : Nat , collatz (6 * n + 4) → collatz (2 * n + 1)
