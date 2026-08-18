import Proofs.Erdos85BinarySquareRegularParity

/-! # Pointwise equitability of owner-color component blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every owner-color graph is pointwise equitable across the defect-component
partition.  From a vertex in normalized part `e`, owner color `c` has
`m_c (m_e-1)` neighbors inside `e`, and `m_c m_f` neighbors in another part
`f`.  The existing quotient theorem only stated this for a chosen component
representative; this form is suitable for rooted path counts. -/
theorem binarySquare_regular_componentOwnerGraph_blockNeighborCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (c e f : (secondOrderDefectGraph G).ConnectedComponent) (x : e.supp) :
    (componentNeighborFinset
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (secondOrderDefectGraph G) f x.1).card =
        if e = f then m c * (m f - 1) else m c * m f := by
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D c
  by_cases hef : e = f
  · subst f
    rw [if_pos rfl]
    have hfin : componentNeighborFinset O D e x.1 =
        (e.supp.toFinite.toFinset).filter fun y =>
          y ≠ x.1 ∧ (componentNeighborFinset G D c x.1 ∩
            componentNeighborFinset G D c y).Nonempty := by
      ext y
      simp [componentNeighborFinset, O, componentOwnerGraph_adj,
        SimpleGraph.mem_neighborFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff, ne_comm, D,
        and_left_comm, and_comm]
    rw [hfin]
    exact binarySquare_regular_sameComponent_ownerCoordinate_card
      G hfree hq hreg hcard e c (hm c) (hm e) x
  · rw [if_neg hef]
    have hxComp : D.connectedComponentMk x.1 = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e x.1).mp x.2
    have hfin : componentNeighborFinset O D f x.1 =
        (f.supp.toFinite.toFinset).filter fun y =>
          (componentNeighborFinset G D c x.1 ∩
            componentNeighborFinset G D c y).Nonempty := by
      ext y
      constructor
      · intro hy
        rw [componentNeighborFinset, Finset.mem_filter] at hy
        have hyAdj : O.Adj x.1 y := (O.mem_neighborFinset x.1 y).mp hy.1
        apply Finset.mem_filter.mpr
        exact ⟨by
          simpa using (SimpleGraph.ConnectedComponent.mem_supp_iff f y).mpr hy.2,
          hyAdj.2⟩
      · intro hy
        have hyData := Finset.mem_filter.mp hy
        have hyComp : D.connectedComponentMk y = f :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff f y).mp
            (by simpa using hyData.1)
        have hxy : x.1 ≠ y := by
          intro h
          subst y
          exact hef (hxComp.symm.trans hyComp)
        rw [componentNeighborFinset]
        exact Finset.mem_filter.mpr
          ⟨(O.mem_neighborFinset x.1 y).mpr ⟨hxy, hyData.2⟩, hyComp⟩
    rw [hfin]
    exact binarySquare_regular_crossComponent_ownerCoordinate_card
      G hfree hq hreg hcard e f c hef (hm c) (hm f) x

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_componentOwnerGraph_blockNeighborCard
