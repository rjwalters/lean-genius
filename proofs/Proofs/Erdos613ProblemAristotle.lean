/-
  Aristotle targets for Erdos613Problem (Erdős #613: Graph Decomposition and Size Ramsey Numbers)
  Routine supporting lemmas for automated proof search.
  See Erdos613Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem or counterexample constructions requiring deep graph theory
  - NOT results depending on def-sorries (starGraph, sizeRamseyStarOddCycle, ramseyNumber)
  - Structural/logical results provable from axioms or elementary arithmetic

  Targets:
  1. original_conjecture_false': The original conjecture is false.
     Follows directly from tao_counterexample_n5 axiom:
     - intro h
     - obtain ⟨V, _, _, G, hcard, hdecomp⟩ := tao_counterexample_n5
     - exact hdecomp (h 5 (by norm_num) V G hcard)

  2. critical_edge_count_formula': Arithmetic identity for criticalEdgeCount.
     criticalEdgeCount n = (2n+1).choose 2 - n.choose 2 - 1
                         = n*(2n+1) - n*(n-1)/2 - 1
                         = 3n(n+1)/2 - 1
                         = n*n + n + n*(n+1)/2 - 1
     Proof strategy: unfold criticalEdgeCount, use simp with Nat.choose lemmas,
     then omega or ring to close the arithmetic.

  Excluded (deep results or depend on def-sorries):
  - original_conjecture_false itself (retry after excluding def-sorry deps)
  - smallest_counterexample: first conjunct requires n=3, n=4 cases (deep graph theory)
  - gap_growth: Real.sqrt arithmetic bounds requiring nlinarith + positivity
  - conjecture_error: depends on sizeRamseyStarOddCycle (def sorry)
  - size_ramsey_generalizes: depends on sizeRamseyStarOddCycle and ramseyNumber (def sorries)
  - n3_holds, n4_holds: deep finite graph theory
  - maximal_bipartite_decomposition: requires additional maximality argument beyond HasDecomposition
-/
import Mathlib
import Proofs.Erdos613Problem

namespace Erdos613.Aristotle

open Erdos613

-- ============================================================
-- Aristotle Target 1: original_conjecture_false
-- ============================================================

/-- The original conjecture is false, as a routine consequence of
    Tao's Lean-verified n=5 counterexample axiom.

    Proof sketch:
    1. Assume OriginalConjecture h.
    2. From tao_counterexample_n5 get V, G with the right edge count and ¬HasDecomposition G 5.
    3. Apply h at n=5 (≥ 3) to get HasDecomposition G 5 — contradiction. -/
lemma original_conjecture_false' : ¬OriginalConjecture := by
  intro h
  obtain ⟨V, _, _, G, hcard, hdecomp⟩ := tao_counterexample_n5
  exact hdecomp (h 5 (by norm_num) V G hcard)

-- ============================================================
-- Aristotle Target 2: critical_edge_count_formula
-- ============================================================

/-- Arithmetic identity: C(2n+1,2) - C(n,2) - 1 = n*n + n + n*(n+1)/2 - 1.

    Both sides equal 3*n*(n+1)/2 - 1.
    Proof sketch: simp [criticalEdgeCount, Nat.choose_two_right] then omega. -/
lemma critical_edge_count_formula' (n : ℕ) (hn : n ≥ 1) :
    criticalEdgeCount n = n * n + n + (n * (n + 1)) / 2 - 1 := by
  simp only [criticalEdgeCount, Nat.choose_two_right]
  omega

end Erdos613.Aristotle
