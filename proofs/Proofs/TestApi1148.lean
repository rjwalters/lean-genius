import Mathlib

open Nat

namespace Erdos1148Test

def HasConstRep (n : ℕ) : Prop :=
  ∃ x y z : ℕ, x ^ 2 + y ^ 2 = n + z ^ 2 ∧ x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n

-- n=23: x,y,z ≤ 4 (5³ = 125 cases). omega should close all goals
-- since after interval_cases all three are concrete numerals.
theorem not_hasConstRep_23 : ¬ HasConstRep 23 := by
  intro ⟨x, y, z, heq, hx, hy, hz⟩
  have : x ≤ 4 := by nlinarith [sq_nonneg x]
  have : y ≤ 4 := by nlinarith [sq_nonneg y]
  have : z ≤ 4 := by nlinarith [sq_nonneg z]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> omega

end Erdos1148Test
