import Proofs.Erdos85OrderSixtyFourRoutingLiftPairDichotomy
import Proofs.Erdos85BinarySquareRoutingExactLiftStar
import Proofs.Erdos85BinarySquareSizeTwoCrossBlockNoRectangle

/-! # Ambient-center form of the paired routing-lift dichotomy -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- For two same-color direct routes from a common root, the direct ambient
centers either coincide, are adjacent in the middle-component owner factor,
or have disjoint middle-component rows which saturate the routing row. -/
theorem orderSixtyFour_twoClosingRoutes_center_eq_or_ownerAdj_or_union_eq_row
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {d e f₁ f₂ c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂)
    (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (x : d.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hdirect₁ : c = crossIntermediateComponent G hfree hdf₁ x z₁)
    (hdirect₂ : c = crossIntermediateComponent G hfree hdf₂ x z₂)
    (hallTwo : ∀ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) :
    let u₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
      rw [hdirect₁]
      exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
    let u₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
      rw [hdirect₂]
      exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
    let R := (Finset.univ : Finset e.supp).filter fun y =>
      c = crossIntermediateComponent G hfree hde x y
    u₁ = u₂ ∨
      (restrictedComponentOwnerGraph G c e).Adj u₁ u₂ ∨
      componentCrossNeighborFinset G e u₁ ∪
        componentCrossNeighborFinset G e u₂ = R := by
  classical
  let u₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
    rw [hdirect₁]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
  let u₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
    rw [hdirect₂]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
  let R := (Finset.univ : Finset e.supp).filter fun y =>
    c = crossIntermediateComponent G hfree hde x y
  let L₁ := R.filter fun y =>
    c = crossIntermediateComponent G hfree hef₁ y z₁
  let L₂ := R.filter fun y =>
    c = crossIntermediateComponent G hfree hef₂ y z₂
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hexact₁ := hallTwo d c e f₁ hde hef₁ hdf₁ x z₁ hdirect₁
  have hexact₂ := hallTwo d c e f₂ hde hef₂ hdf₂ x z₂ hdirect₂
  have hL₁star : L₁ = componentCrossNeighborFinset G e u₁ := by
    have hstar :=
      binarySquare_regular_sizeTwoRoutingColor_exact_lifts_eq_starCompletions
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hde hef₁ hdf₁ (by simpa using hall e) x z₁ hdirect₁ hexact₁
    calc
      L₁ = ((Finset.univ : Finset e.supp).filter fun y =>
          c = crossIntermediateComponent G hfree hde x y ∧
            c = crossIntermediateComponent G hfree hef₁ y z₁) := by
        ext y
        simp only [L₁, R, Finset.mem_filter, Finset.mem_univ, true_and]
      _ = componentCrossNeighborFinset G e u₁ := by
        simpa only [u₁] using hstar
  have hL₂star : L₂ = componentCrossNeighborFinset G e u₂ := by
    have hstar :=
      binarySquare_regular_sizeTwoRoutingColor_exact_lifts_eq_starCompletions
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          hde hef₂ hdf₂ (by simpa using hall e) x z₂ hdirect₂ hexact₂
    calc
      L₂ = ((Finset.univ : Finset e.supp).filter fun y =>
          c = crossIntermediateComponent G hfree hde x y ∧
            c = crossIntermediateComponent G hfree hef₂ y z₂) := by
        ext y
        simp only [L₂, R, Finset.mem_filter, Finset.mem_univ, true_and]
      _ = componentCrossNeighborFinset G e u₂ := by
        simpa only [u₂] using hstar
  have hpairs :=
    orderSixtyFour_twoClosingRoutes_lift_inter_nonempty_or_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hdirect₁ hdirect₂ hallTwo
  change (L₁ ∩ L₂).Nonempty ∨ L₁ ∪ L₂ = R at hpairs
  rw [hL₁star, hL₂star] at hpairs
  rcases hpairs with hinter | hsaturate
  · by_cases hu : u₁ = u₂
    · exact Or.inl hu
    · exact Or.inr <| Or.inl <|
        (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
          G c e u₁ u₂).mpr ⟨hu, hinter⟩
  · exact Or.inr (Or.inr hsaturate)

end

end Erdos85
