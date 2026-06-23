/-
  Aristotle targets for Erdős Problem #636
  Routine supporting lemmas for automated proof search.
  See Erdos636Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Kwan-Sudakov 2021) or the axiomatized bounds
  - Routine consequences of the signature/edge-count definitions
  - No definition sorries, no axioms

  Targets included (3 theorem sorries):
  1. edge_count_range   — edges in an induced subgraph ≤ complete graph on same vertices
  2. clique_few_signatures — complete graph: at most n+1 distinct signatures
  3. empty_few_signatures  — empty graph: at most n+1 distinct signatures

  Excluded:
  - CountDistinctIsomorphismTypes: def sorry, Aristotle skips definitions
  - kwan_sudakov / signature_upper_bound: axioms, not theorem sorries
  - theta_bound: depends on the axioms above
-/

import Mathlib

namespace Erdos636.Aristotle

open Finset Function Nat SimpleGraph

/-
## Mirrored Definitions

Reproduced verbatim from Erdos636Problem.lean so Aristotle can work with them directly.
-/

/-- The number of edges in an induced subgraph. -/
noncomputable def inducedEdgeCount [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.induce (↑S : Set V)).edgeFinset.card

/-- The signature of an induced subgraph: (vertex count, edge count). -/
def Signature := ℕ × ℕ

/-- Get the signature of an induced subgraph. -/
noncomputable def getSignature [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Signature :=
  (S.card, inducedEdgeCount G S)

/-- The set of all induced subgraph signatures of G. -/
noncomputable def allSignatures [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset Signature :=
  (Finset.univ : Finset (Finset V)).image (getSignature G)

/-- The number of distinct signatures. -/
noncomputable def distinctSignatureCount [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (allSignatures G).card

/-
## Aristotle Targets
-/

/-- The edge count of an induced subgraph is at most v*(v-1)/2 where v = |S|.
    This is the edge count of the complete graph on |S| vertices. -/
theorem edge_count_range [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedEdgeCount G S ≤ S.card * (S.card - 1) / 2 := by
  sorry

/-- The complete graph on Fin n has at most n+1 distinct signatures.
    Every size-k subset induces a complete graph with k*(k-1)/2 edges,
    so the signature depends only on k, giving at most n+1 possible signatures. -/
theorem clique_few_signatures (n : ℕ) :
    distinctSignatureCount (⊤ : SimpleGraph (Fin n)) ≤ n + 1 := by
  sorry

/-- The empty graph on Fin n has at most n+1 distinct signatures.
    Every subset has 0 edges, so the signature is (k, 0) for k = 0, …, n,
    giving at most n+1 distinct signatures. -/
theorem empty_few_signatures (n : ℕ) :
    distinctSignatureCount (⊥ : SimpleGraph (Fin n)) ≤ n + 1 := by
  sorry

end Erdos636.Aristotle
