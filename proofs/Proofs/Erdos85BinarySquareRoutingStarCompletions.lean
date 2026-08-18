import Proofs.Erdos85BinarySquareRoutingTriangleLift
import Proofs.Erdos85BinarySquareSizeTwoCrossIndexedBlocks

/-! # Canonical star completions of routing edges -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A specified common neighbor determines the routing component. -/
theorem crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) {y : V}
    (hy : G.Adj x.1 y ∧ G.Adj z.1 y) :
    crossIntermediateComponent G hfree hce x z =
      (secondOrderDefectGraph G).connectedComponentMk y := by
  have heq : y = crossCommonNeighbor G hfree hce x z :=
    eq_crossCommonNeighbor_of_adj G hfree hce x z hy
  have hmem := crossCommonNeighbor_mem_intermediate G hfree hce x z
  rw [heq]
  exact ((ConnectedComponent.mem_supp_iff _ _).mp hmem).symm

/-- The unique common neighbor of a direct routing edge has exactly two
neighbors in every normalized size-two third component.  Those two vertices
are canonical monochromatic star completions of the edge. -/
theorem binarySquare_regular_sizeTwoPart_exists_two_routingStarCompletions
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    {c e f d : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (he : e.supp.ncard = q * 2)
    (x : c.supp) (w : f.supp)
    (hxw : crossIntermediateComponent G hfree hcf x w = d) :
    ∃ y : d.supp,
      (componentCrossNeighborFinset G e y).card = 2 ∧
      ∀ z ∈ componentCrossNeighborFinset G e y,
        crossIntermediateComponent G hfree hce x z = d ∧
          crossIntermediateComponent G hfree hef z w = d := by
  let y₀ := crossCommonNeighbor G hfree hcf x w
  have hy₀memRoute := crossCommonNeighbor_mem_intermediate G hfree hcf x w
  have hy₀mem : y₀ ∈ d.supp := by
    rw [← hxw]
    exact hy₀memRoute
  let y : d.supp := ⟨y₀, hy₀mem⟩
  refine ⟨y, ?_, ?_⟩
  · rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard e he y.1
  · intro z hz
    have hyz : G.Adj y.1 z.1 := by
      exact (Finset.mem_filter.mp hz).2
    have hy₀ := crossCommonNeighbor_spec G hfree hcf x w
    have hycomp : (secondOrderDefectGraph G).connectedComponentMk y.1 = d :=
      (ConnectedComponent.mem_supp_iff d y.1).mp y.2
    constructor
    · calc
        crossIntermediateComponent G hfree hce x z =
            (secondOrderDefectGraph G).connectedComponentMk y.1 :=
          crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
            G hfree hce x z ⟨hy₀.1, hyz.symm⟩
        _ = d := hycomp
    · calc
        crossIntermediateComponent G hfree hef z w =
            (secondOrderDefectGraph G).connectedComponentMk y.1 :=
          crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
            G hfree hef z w ⟨hyz.symm, hy₀.2⟩
        _ = d := hycomp

end

end Erdos85
