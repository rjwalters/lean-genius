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

/-- Comparison lemma for reciprocal logarithmic sums.
    If a ≤ C·b and a ≥ 2C (so b ≥ a/C ≥ 2), then
    b·log(b) ≥ (a/C)·log(a/C) ≥ a·log(a)/(2C) for large a.
    Hence 1/(b·log b) ≤ 2C/(a·log a). -/
theorem reciprocal_log_comparison (a_n b_n C : ℕ) (hC : C > 0)
    (hdom : a_n ≤ C * b_n) (ha : a_n ≥ 2) (hb : b_n ≥ 2)
    (hlarge : a_n ≥ 2 * C) :
    (1 : ℝ) / ((b_n : ℝ) * Real.log (b_n : ℝ))
      ≤ 2 * C / ((a_n : ℝ) * Real.log (a_n : ℝ)) := by sorry

/-- For a, C : ℕ with a ≤ C·b and C > 0, we have b ≥ 1. -/
theorem dominated_implies_b_pos (a b C : ℕ) (hC : C > 0) (hdom : a ≤ C * b) (ha : a ≥ 2) :
    b ≥ 1 := by sorry

/-- log is monotone: if a ≤ b, then log a ≤ log b (for positive reals). -/
theorem log_mono_nat (a b : ℕ) (ha : a ≥ 2) (hab : a ≤ b) :
    Real.log (a : ℝ) ≤ Real.log (b : ℝ) := by sorry

end Erdos892Aristotle
