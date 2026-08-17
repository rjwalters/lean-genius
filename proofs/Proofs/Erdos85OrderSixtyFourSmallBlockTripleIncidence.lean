import Proofs.Erdos85CrossDefectComponentCommonNeighbor
import Proofs.Erdos85OrderSixtyFourSmallBlockCrossMatching

/-! # Three-block incidence in the order-64 reduced design -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Each vertex of a target small block determines a unique ordered pair of
neighbors in any two source small blocks.  Thus each target block contributes
eight cells to the source blocks' `8 × 8` grid. -/
theorem orderSixtyFour_seven_defect_components_smallBlockTriple_unique_incidence
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
          ∀ k, k ≠ c → k.supp.ncard = 8 ∧
            ∀ z : k.supp, ∃! p : e.supp × f.supp,
              G.Adj p.1.1 z.1 ∧ G.Adj p.2.1 z.1 := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_smallBlocks_unique_neighbor
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecross⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcross⟩ := hsmall f hfc
  refine ⟨hf8, ?_⟩
  intro k hkc
  obtain ⟨hk8, hkcross⟩ := hsmall k hkc
  refine ⟨hk8, ?_⟩
  intro z
  obtain ⟨x, hx, hxuniq⟩ := (hkcross e hec).2 z
  obtain ⟨y, hy, hyuniq⟩ := (hkcross f hfc).2 z
  refine ⟨(x, y), ⟨hx.symm, hy.symm⟩, ?_⟩
  intro p hp
  apply Prod.ext
  · exact hxuniq p.1 hp.1.symm
  · exact hyuniq p.2 hp.2.symm

/-- The completion-to-cell assignment is injective: two common neighbors of
the same cross-component label pair coincide. -/
theorem crossDefectComponent_common_completion_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hef : e ≠ f) (x : e.supp) (y : f.supp) {z w : V}
    (hz : G.Adj x.1 z ∧ G.Adj y.1 z)
    (hw : G.Adj x.1 w ∧ G.Adj y.1 w) : z = w := by
  obtain ⟨q, hq, huniq⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hef x y
  exact (huniq z hz).trans (huniq w hw).symm

end

end Erdos85
