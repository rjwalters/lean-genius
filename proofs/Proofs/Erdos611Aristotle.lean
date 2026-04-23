/-
  Aristotle targets for Erdős Problem #611 (Clique Transversal with Large Cliques)
  Routine supporting lemmas for automated proof search.
  See Erdos611Problem.lean for the main formalization.

  Included:
  - refines_610: direct consequence of erdos_gallai_tuza_large_cliques with k=2;
    the first hypothesis is unused — apply the axiom to hLarge directly
  - linear_cliques_sublinear: AllCliquesLinear G c implies AllCliquesLarge G ⌈c·n⌉,
    then erdos_gallai_tuza_large_cliques with k = ⌈c·n⌉ gives τ G ≤ n - √(⌈c·n⌉·n)
    ≤ n - √c·n = (1-√c)·n
  - question1_positive: follows from linear_cliques_sublinear and Real.sqrt_lt_one

  Excluded:
  - cliqueTransversalNumber, k_threshold, minMaximalCliqueSize (def sorries)
  - complete_graph_tau, complete_bipartite_tau, turan_graph_tau (τ sorry-def)
  - threshold_grows_slowly (depends on k_threshold sorry-def)
-/
import Mathlib
import Proofs.Erdos611Problem

namespace Erdos611Aristotle

open Erdos611 SimpleGraph Finset Real

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The first hypothesis is unused: apply erdos_gallai_tuza_large_cliques with k=2
    to hLarge to obtain τ G ≤ n - √(2·n) directly. -/
theorem refines_610 :
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (τ G : ℝ) ≤ Fintype.card V - Real.sqrt (2 * Fintype.card V) + 10) →
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      AllCliquesLarge G 2 →
      (τ G : ℝ) ≤ Fintype.card V - Real.sqrt (2 * Fintype.card V)) := by
  sorry

/-- AllCliquesLinear G c → AllCliquesLarge G ⌈c·n⌉ → τ G ≤ n - √(⌈c·n⌉·n) ≤ (1-√c)·n -/
theorem linear_cliques_sublinear (c : ℝ) (hc : 0 < c) (hc' : c ≤ 1) :
    ∀ (W : Type*) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      AllCliquesLinear G c →
      (τ G : ℝ) ≤ (1 - Real.sqrt c) * Fintype.card W := by
  sorry

/-- For 0 < c < 1, (1 - √c) < 1, so τ G ≤ (1-√c)·n < n -/
theorem question1_positive :
    ∀ c : ℝ, 0 < c → c < 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
        AllCliquesLinear G c →
        (τ G : ℝ) < Fintype.card W := by
  sorry

end Erdos611Aristotle
