/-
  Aristotle targets for Erdős Problem #613
  Routine supporting lemmas for automated proof search.
  See Erdos613Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main disproof results (Pikhurko, Tao) — cited research results
  - NOT theorems depending on axioms (pikhurko_*, tao_counterexample_n5, faudree_partial)
  - NOT theorems depending on sorry definitions (sizeRamseyStarOddCycle, ramseyNumber)
  - Standalone arithmetic identity

  Included targets (1):
  - critical_edge_count_formula: C(2n+1,2) - C(n,2) - 1 = n² + n + n(n+1)/2 - 1
-/
import Mathlib

namespace Erdos613ProblemAristotle

open Nat

/-- The critical edge count from the problem: C(2n+1,2) - C(n,2) - 1 -/
def criticalEdgeCount (n : ℕ) : ℕ :=
  (2*n + 1).choose 2 - n.choose 2 - 1

-- Routine: simplified form of the critical edge count.
-- C(2n+1,2) - C(n,2) - 1 = 3n(n+1)/2 - 1 = n² + n + n(n+1)/2 - 1
theorem critical_edge_count_formula (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n = n * n + n + (n * (n + 1)) / 2 - 1 := by
  sorry

end Erdos613ProblemAristotle
