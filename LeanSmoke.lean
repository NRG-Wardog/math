import Lean

namespace GenericProofs

set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem max_budget (a b c : Nat) (ha : a ≤ c) (hb : b ≤ c) :
    max a b ≤ c :=
  Nat.max_le_of_le_of_le ha hb

theorem sum_budget (a b c d : Nat) (ha : a ≤ c) (hb : b ≤ d) :
    a + b ≤ c + d := by omega

theorem and_true (a b : Bool) (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb] <;> rfl

#print axioms max_budget
#print axioms sum_budget
#print axioms and_true

end GenericProofs
