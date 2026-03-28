/-
  Aristotle targets for Erdos Problem #892
  Routine supporting lemmas for automated proof search.
  See Erdos892Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Real

namespace Erdos892Aristotle

/-- For a, C : ℕ with a ≤ C·b and C > 0, we have b ≥ 1. -/
theorem dominated_implies_b_pos (a b C : ℕ) (hC : C > 0) (hdom : a ≤ C * b) (ha : a ≥ 2) :
    b ≥ 1 := by
  by_contra h; push_neg at h
  interval_cases b; simp at hdom; omega

/-- log is monotone: if a ≤ b, then log a ≤ log b (for positive reals). -/
theorem log_mono_nat (a b : ℕ) (ha : a ≥ 2) (hab : a ≤ b) :
    Real.log (a : ℝ) ≤ Real.log (b : ℝ) := by
  apply Real.log_le_log (by positivity) (by exact_mod_cast hab)

end Erdos892Aristotle
