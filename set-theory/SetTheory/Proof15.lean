import SetTheory
open Set

theorem diff_inter_snd_empty (A B: Set α ) : (A \ B) ∩ B = ∅ := by
  apply Set.ext
  intro x
  constructor
  . intro hab
    have hd := hab.left.right
    have hb := hab.right
    contradiction
  . intro he
    contradiction
