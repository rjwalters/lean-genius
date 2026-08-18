import Proofs.Erdos85FixedVertexCyclicTriangleCount

/-!
# The all-triangle-free size-two residue socket

For a normalized size-two defect component, the ambient graph induced on the
component is two-regular.  Hence triangle-free degree two already says that
all internal ambient edges are triangle-free; it is not a separate premise.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a normalized size-two defect component, triangle-free degree two at
every component vertex forces every internal ambient edge to be
triangle-free. -/
theorem binarySquare_regular_sizeTwoPart_internal_adj_triangleFree_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (htfdegree : ∀ x ∈ c.supp,
      (triangleFreeEdgeGraph G).degree x = 2) :
    ∀ ⦃x y : V⦄, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y := by
  intro x y hx hy hxy
  let xs : c.supp := ⟨x, hx⟩
  have hsub : triangleFreeNeighbors G x ⊆
      componentNeighborFinset G (secondOrderDefectGraph G) c x :=
    triangleFreeNeighbors_subset_componentNeighborFinset G c hx
  have htfcard : (triangleFreeNeighbors G x).card = 2 := by
    rw [← triangleFreeEdgeGraph_neighborFinset,
      (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      htfdegree x hx]
  have hcomponentCard :
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2 := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard c c (x := x) hx
    rw [hc] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have heq : triangleFreeNeighbors G x =
      componentNeighborFinset G (secondOrderDefectGraph G) c x := by
    apply Finset.eq_of_subset_of_card_le hsub
    omega
  have hymem : y ∈
      componentNeighborFinset G (secondOrderDefectGraph G) c x := by
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset x y).mpr hxy,
      (ConnectedComponent.mem_supp_iff c y).mp hy⟩
  exact (triangleFreeEdgeGraph_adj G x y).mpr (heq.symm ▸ hymem)

/-- At order 64, the two-component modular residue endpoint for an
all-triangle-free normalized size-two component needs only the degree-two
formulation of that condition. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_allTf
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (htfdegree : ∀ x ∈ c.supp,
      (triangleFreeEdgeGraph G).degree x = 2) :
    192 ∣ ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply
    orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_tfdegree_two
      G hfree hreg hcard m hm hsum hcount c hc
  · intro x y hx hy hxy
    exact binarySquare_regular_sizeTwoPart_internal_adj_triangleFree_of_degree_two
      G hfree (q := 8) (by norm_num) hreg (by simpa using hcard)
        c (by simpa using hc) htfdegree hx hy hxy
  · exact htfdegree

end

end Erdos85

#print axioms
  Erdos85.binarySquare_regular_sizeTwoPart_internal_adj_triangleFree_of_degree_two
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_allTf
