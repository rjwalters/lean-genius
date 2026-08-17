import Proofs.Erdos85BinarySquareRoutingStarCompletions

/-! # Exact routing lifts are precisely the canonical star completions -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- When a monochromatic routing-lift fiber has the minimum cardinality two,
it is exactly the intermediate-component neighbor row of the direct edge's
unique ambient common-neighbor center. -/
theorem binarySquare_regular_sizeTwoRoutingColor_exact_lifts_eq_starCompletions
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
    (hroute : d = crossIntermediateComponent G hfree hcf x w)
    (hexact : ((Finset.univ : Finset e.supp).filter fun z =>
      d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w).card = 2) :
    let y₀ := crossCommonNeighbor G hfree hcf x w
    let y : d.supp := ⟨y₀, by
      rw [hroute]
      exact crossCommonNeighbor_mem_intermediate G hfree hcf x w⟩
    ((Finset.univ : Finset e.supp).filter fun z =>
      d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w) =
      componentCrossNeighborFinset G e y := by
  classical
  let L := (Finset.univ : Finset e.supp).filter fun z =>
    d = crossIntermediateComponent G hfree hce x z ∧
      d = crossIntermediateComponent G hfree hef z w
  let y₀ := crossCommonNeighbor G hfree hcf x w
  have hy₀mem : y₀ ∈ d.supp := by
    rw [hroute]
    exact crossCommonNeighbor_mem_intermediate G hfree hcf x w
  let y : d.supp := ⟨y₀, hy₀mem⟩
  have hstarCard : (componentCrossNeighborFinset G e y).card = 2 := by
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard e he y.1
  have hstarSub : componentCrossNeighborFinset G e y ⊆ L := by
    intro z hz
    have hyz : G.Adj y.1 z.1 := (Finset.mem_filter.mp hz).2
    have hy₀ := crossCommonNeighbor_spec G hfree hcf x w
    have hycomp : (secondOrderDefectGraph G).connectedComponentMk y.1 = d :=
      (ConnectedComponent.mem_supp_iff d y.1).mp y.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · symm
      calc
        crossIntermediateComponent G hfree hce x z =
            (secondOrderDefectGraph G).connectedComponentMk y.1 :=
          crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
            G hfree hce x z ⟨hy₀.1, hyz.symm⟩
        _ = d := hycomp
    · symm
      calc
        crossIntermediateComponent G hfree hef z w =
            (secondOrderDefectGraph G).connectedComponentMk y.1 :=
          crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
            G hfree hef z w ⟨hyz.symm, hy₀.2⟩
        _ = d := hycomp
  have heq : componentCrossNeighborFinset G e y = L :=
    Finset.eq_of_subset_of_card_le hstarSub (by rw [hstarCard, hexact])
  exact heq.symm

end

end Erdos85
