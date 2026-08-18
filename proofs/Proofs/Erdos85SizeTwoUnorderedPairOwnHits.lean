import Proofs.Erdos85SizeTwoUnorderedPairHitLaw

/-! # Hits at the endpoints of an occupied unordered pair

The label-free hit law has a particularly sharp specialization at the two
endpoints selected by an outside vertex: either the endpoints are adjacent
and neither endpoint is served by an exterior neighbour, or they are
nonadjacent and each endpoint is served uniquely.  This is the first half of
the own-pair neighbour count in the eigenline-free model.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An endpoint of an outside owner's selected pair has a unique exterior
common neighbour with the owner exactly when the two selected endpoints are
nonadjacent.  The statement is symmetric in the two endpoints. -/
theorem outsidePair_endpoint_unique_hits_iff_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (u : {x : V // x ∉ c.supp}) (z z' : c.supp)
    (hpair : (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset =
      {z, z'}) :
    ((∃! y, G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj z.1 y) ↔
      ¬ G.Adj z.1 z'.1) ∧
    ((∃! y, G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj z'.1 y) ↔
      ¬ G.Adj z.1 z'.1) := by
  have hz := existsUnique_exterior_common_iff_outsidePair_forall_not_adj
    G hfree c hcard u z
  have hz' := existsUnique_exterior_common_iff_outsidePair_forall_not_adj
    G hfree c hcard u z'
  constructor
  · rw [hz, hpair]
    simp
  · rw [hz', hpair]
    simp [G.adj_comm]

#print axioms Erdos85.outsidePair_endpoint_unique_hits_iff_not_adj

end

end Erdos85
