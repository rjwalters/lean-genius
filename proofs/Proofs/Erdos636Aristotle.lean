/-
  Aristotle targets for Erdős Problem #636
  Routine supporting lemmas for automated proof search.
  See Erdos636Problem.lean for the main formalization.

  Criteria for inclusion:
  - edge_count_range: induced edge count ≤ choose 2 of vertex count
  - inducedEdgeCount_empty: empty graph has 0 edges in any induced subgraph
  - clique_few_signatures: complete graph has ≤ n+1 distinct signatures
    (all induced subgraphs with same vertex count have same signature)
  - empty_few_signatures: empty graph has ≤ n+1 distinct signatures
    (all induced subgraphs with same vertex count have signature (k, 0))
  - NOT kwan_sudakov (axiom — major result)
  - NOT signature_upper_bound (axiom — major result)
  - NOT CountDistinctIsomorphismTypes (definition sorry)
-/
import Mathlib

namespace Erdos636Aristotle

open SimpleGraph Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges in an induced subgraph. -/
noncomputable def inducedEdgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.induce (↑S : Set V)).edgeFinset.card

/-- The signature of an induced subgraph: (vertex count, edge count). -/
def Signature := ℕ × ℕ

/-- Get the signature of an induced subgraph. -/
noncomputable def getSignature (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Signature :=
  (S.card, inducedEdgeCount G S)

/-- The set of all induced subgraph signatures of G. -/
noncomputable def allSignatures (G : SimpleGraph V) [DecidableRel G.Adj] : Finset Signature :=
  (Finset.univ : Finset (Finset V)).image (getSignature G)

/-- The number of distinct signatures. -/
noncomputable def distinctSignatureCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (allSignatures G).card

-- Routine: The empty graph has no edges, so any induced subgraph has 0 edges.
-- The empty graph's edge set is ∅, and the induced subgraph inherits no edges.
theorem inducedEdgeCount_empty (S : Finset V) :
    inducedEdgeCount (⊥ : SimpleGraph V) S = 0 := by
  sorry

-- Routine: Two subsets of the same size yield the same signature in the complete graph.
-- In ⊤, all edges between vertices in S exist, so the count depends only on S.card.
theorem getSignature_top_eq_of_card_eq (S T : Finset (Fin n)) (h : S.card = T.card) :
    getSignature (⊤ : SimpleGraph (Fin n)) S = getSignature ⊤ T := by
  sorry

-- Routine: Two subsets of the same size yield the same signature in the empty graph.
-- In ⊥, there are no edges, so getSignature ⊥ S = (S.card, 0) for all S.
theorem getSignature_bot_eq_of_card_eq (S T : Finset (Fin n)) (h : S.card = T.card) :
    getSignature (⊥ : SimpleGraph (Fin n)) S = getSignature ⊥ T := by
  sorry

-- Routine: The induced edge count is at most C(|S|, 2) = |S|*(|S|-1)/2.
-- Each pair of vertices in S contributes at most 1 edge.
theorem edge_count_range (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedEdgeCount G S ≤ S.card * (S.card - 1) / 2 := by
  sorry

-- Routine: The complete graph on Fin n has at most n+1 distinct induced subgraph signatures.
-- Any two subsets of the same size have the same signature in ⊤, so there are at most
-- n+1 signatures (one for each cardinality 0, 1, ..., n).
theorem clique_few_signatures (n : ℕ) :
    distinctSignatureCount (⊤ : SimpleGraph (Fin n)) ≤ n + 1 := by
  sorry

-- Routine: The empty graph on Fin n has at most n+1 distinct induced subgraph signatures.
-- Every induced subgraph has signature (k, 0), where k = S.card ∈ {0, ..., n}.
theorem empty_few_signatures (n : ℕ) :
    distinctSignatureCount (⊥ : SimpleGraph (Fin n)) ≤ n + 1 := by
  sorry

end Erdos636Aristotle
