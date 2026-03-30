/-
  Aristotle targets for StirlingExpansion
  Higher-order Stirling expansion terms for automated proof search.
  See StirlingExpansion.lean for the main formalization.

  Criteria for inclusion:
  - Well-known asymptotic analysis results
  - Stirling first correction and two-term expansion
  - Clean theorem statements with no definition sorries
  - No axioms, no open conjectures
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace StirlingExpansion

open Stirling Real Filter

/-- Stirling's First Correction:
    stirlingSeq(n)/√π = 1 + 1/(12n) + O(1/n²). -/
theorem stirling_first_correction :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |stirlingSeq n / Real.sqrt π - (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2 := by
  sorry

/-- Stirling Two-Term Expansion:
    n! = √(2πn)·(n/e)^n · (1 + 1/(12n) + O(1/n²)). -/
theorem stirling_two_term_expansion :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |(n.factorial : ℝ) / (Real.sqrt (2 * π * n) * ((n : ℝ) / Real.exp 1) ^ n) -
        (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2 := by
  sorry

end StirlingExpansion
