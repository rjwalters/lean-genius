import Proofs.Erdos85SizeTwoUnorderedPairOwnHits

/-! # Distinctness of the two own-pair endpoint hits -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exterior common neighbours serving the two distinct endpoints of one
outside owner's selected pair cannot coincide.  Otherwise the endpoints
would have both the owner and the coincident hit as common neighbours, which
violates C4-freeness. -/
theorem outsidePair_endpoint_exterior_common_ne
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
      {z, z'}) (hzz' : z ≠ z')
    {y y' : V}
    (hy : G.Adj u.1 y ∧ y ∉ c.supp ∧ G.Adj z.1 y)
    (hy' : G.Adj u.1 y' ∧ y' ∉ c.supp ∧ G.Adj z'.1 y') :
    y ≠ y' := by
  intro hyy'
  subst y'
  have hzmem : z ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset := by
    rw [hpair]
    simp
  have hz'mem : z' ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard u).toFinset := by
    rw [hpair]
    simp
  have hzu : G.Adj z.1 u.1 :=
    (mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard u z).mp hzmem
  have hz'u : G.Adj z'.1 u.1 :=
    (mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard u z').mp hz'mem
  have humem : u.1 ∈ G.neighborFinset z.1 ∩ G.neighborFinset z'.1 := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hzu, hz'u⟩
  have hymem : y ∈ G.neighborFinset z.1 ∩ G.neighborFinset z'.1 := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hy.2.2, hy'.2.2⟩
  have huy : u.1 ≠ y := G.ne_of_adj hy.1
  have heq := Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree z.1 z'.1
      (fun h ↦ hzz' (Subtype.ext h)))
    u.1 humem y hymem
  exact huy heq

#print axioms Erdos85.outsidePair_endpoint_exterior_common_ne

end

end Erdos85
