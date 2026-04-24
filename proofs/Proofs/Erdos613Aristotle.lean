/-
  Aristotle companion for Erdős Problem #613: Graph Decomposition and Size Ramsey Numbers

  This file exposes routine lemmas for automated proof search by Aristotle.
  The main formalization is in Erdos613Problem.lean.

  Targets: arithmetic lemmas about criticalEdgeCount that do not depend on
  sorry-defined graph functions.
-/

import Mathlib
import Proofs.Erdos613Problem

namespace Erdos613Aristotle

open Erdos613 Nat

/-- criticalEdgeCount equals 3n(n+1)/2 - 1 (equivalently n²+n+n(n+1)/2-1).
    This is a pure binomial coefficient identity: C(2n+1,2) - C(n,2) - 1. -/
theorem critical_edge_count_formula_ari (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n = n * n + n + (n * (n + 1)) / 2 - 1 := by
  sorry

/-- criticalEdgeCount is strictly increasing for n ≥ 1 -/
theorem criticalEdgeCount_mono (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n < criticalEdgeCount (n + 1) := by
  sorry

/-- criticalEdgeCount n ≥ 2 for all n ≥ 1 -/
theorem criticalEdgeCount_pos (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n ≥ 2 := by
  sorry

end Erdos613Aristotle
