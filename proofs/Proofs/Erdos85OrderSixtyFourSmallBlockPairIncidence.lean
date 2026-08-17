import Proofs.Erdos85CrossDefectComponentCommonNeighbor
import Proofs.Erdos85OrderSixtyFourSmallBlockPerfectMatching

/-! # Pair incidence between two small blocks over H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A fixed cross-component label pair cannot be completed by two distinct
vertices of a third component.  This is the injectivity behind the sixteen
H-completed cells. -/
theorem crossDefectComponent_pair_common_incidence_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hef : e ≠ f) (x : e.supp) (y : f.supp) (u v : c.supp)
    (hxu : u.1 ∈ componentNeighborFinset G
      (secondOrderDefectGraph G) c x.1)
    (hyu : u.1 ∈ componentNeighborFinset G
      (secondOrderDefectGraph G) c y.1)
    (hxv : v.1 ∈ componentNeighborFinset G
      (secondOrderDefectGraph G) c x.1)
    (hyv : v.1 ∈ componentNeighborFinset G
      (secondOrderDefectGraph G) c y.1) : u = v := by
  obtain ⟨z, hz, huniq⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hef x y
  have hu : G.Adj x.1 u.1 ∧ G.Adj y.1 u.1 := by
    constructor
    · exact (G.mem_neighborFinset x.1 u.1).mp (Finset.mem_filter.mp hxu).1
    · exact (G.mem_neighborFinset y.1 u.1).mp (Finset.mem_filter.mp hyu).1
  have hv : G.Adj x.1 v.1 ∧ G.Adj y.1 v.1 := by
    constructor
    · exact (G.mem_neighborFinset x.1 v.1).mp (Finset.mem_filter.mp hxv).1
    · exact (G.mem_neighborFinset y.1 v.1).mp (Finset.mem_filter.mp hyv).1
  apply Subtype.ext
  exact (huniq u.1 hu).trans (huniq v.1 hv).symm

/-- For any two small defect blocks and every vertex of H16, there is a
unique ordered pair of labels—one from each block—whose selected H16 pairs
both contain that vertex.  These are the sixteen H-completed cells in the
`8 × 8` grid of label pairs. -/
theorem orderSixtyFour_seven_defect_components_smallBlockPair_unique_incidence
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ f, f ≠ c → f.supp.ncard = 8 ∧
          ∀ u : c.supp, ∃! p : e.supp × f.supp,
            u.1 ∈ componentNeighborFinset G
              (secondOrderDefectGraph G) c p.1.1 ∧
            u.1 ∈ componentNeighborFinset G
              (secondOrderDefectGraph G) c p.2.1 := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_smallBlock_pair_unique_incidence
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, heinc⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfinc⟩ := hsmall f hfc
  refine ⟨hf8, ?_⟩
  intro u
  obtain ⟨x, hx, hxuniq⟩ := heinc u
  obtain ⟨y, hy, hyuniq⟩ := hfinc u
  refine ⟨(x, y), ⟨hx, hy⟩, ?_⟩
  intro p hp
  apply Prod.ext
  · exact hxuniq p.1 hp.1
  · exact hyuniq p.2 hp.2

end

end Erdos85
