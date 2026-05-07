/-
  Aristotle targets for Erdos79Problem
  Routine supporting lemmas for automated proof search.
  See Erdos79Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT axioms (K4_not_linear, K4_subgraphs_linear, ramsey_linear_hereditary,
    wigderson_theorem): Aristotle skips axioms
  - NOT the type-mismatch sorry (K4_unique_known): structural issue, skip
  - Computational result: K4 has exactly 6 edges (decidable)
  - Logical argument: minimal non-linear graphs form an antichain
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (2):
  - K4_edge_count_ari: edgeCount (completeGraph 4) = 6 (by decide)
  - minimal_form_antichain_ari: minimally non-linear graphs are pairwise incomparable

  NOT included:
  - K4_not_linear: axiom (Aristotle skips)
  - K4_subgraphs_linear: axiom (Aristotle skips)
  - ramsey_linear_hereditary: axiom (Aristotle skips)
  - wigderson_theorem: axiom (Aristotle skips)
  - K4_unique_known: requires handling type mismatch (Fin 4 vs ℕ)
-/
import Mathlib
import Proofs.Erdos79Problem

namespace Erdos79ProblemAristotle

open Erdos79 SimpleGraph

/-
## Section 1: Edge Count of K₄

K₄ has 4 vertices, each adjacent to the other 3. The number of
undirected edges is C(4,2) = 6. This is decidable since Fin 4 is
a finite type with decidable equality.
-/

/-- The complete graph on 4 vertices has exactly 6 edges. -/
theorem K4_edge_count_ari : edgeCount (completeGraph 4) = 6 := by
  native_decide

/-
## Section 2: Antichain Property

Minimally non-Ramsey-size-linear graphs form an antichain in the
subgraph ordering. The proof uses only the definition of minimality:
- If G is minimally non-linear and H is minimally non-linear,
  then G cannot be a proper subgraph of H (otherwise H's minimality
  would force G to be Ramsey-size-linear, contradicting G's non-linearity).
- By symmetry, H cannot be a proper subgraph of G.
-/

/-- Minimally non-Ramsey-size-linear graphs are pairwise incomparable
    in the subgraph ordering. -/
theorem minimal_form_antichain_ari :
    ∀ G H : SimpleGraph ℕ,
    isMinimallyNonLinear G → isMinimallyNonLinear H →
    G ≠ H → ¬ isProperSubgraph G H ∧ ¬ isProperSubgraph H G := by
  intro G H ⟨hGsup, hGmin⟩ ⟨hHsup, hHmin⟩ _
  exact ⟨fun hGH => hGsup (hHmin G hGH), fun hHG => hHsup (hGmin H hHG)⟩

end Erdos79ProblemAristotle
