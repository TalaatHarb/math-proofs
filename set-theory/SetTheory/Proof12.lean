import SetTheory
open Set

theorem cross_distribute_inter (A B C: Set α ) : (A × (B ∩ C)) = (A × B) ∩ (A × C):= by
  apply Set.ext
  intro p
  constructor
  . intro habc
    constructor
    . constructor
      . exact habc.left
      . exact And.left habc.right
    . constructor
      . exact habc.left
      . exact And.right habc.right
  . intro habc
    constructor
    . exact (And.left habc).left
    . constructor
      . exact habc.left.right
      . exact habc.right.right
