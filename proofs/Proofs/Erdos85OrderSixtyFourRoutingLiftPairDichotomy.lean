import Proofs.Erdos85OrderSixtyFourRoutingCycleLiftSeparation
import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity

/-! # Pairwise overlap dichotomy for exact routing lifts -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- Two exact two-lift fibers inside the same four-point routing row either
overlap, or partition that row. -/
theorem orderSixtyFour_twoClosingRoutes_lift_inter_nonempty_or_union_eq_row
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
    let R := (Finset.univ : Finset e.supp).filter fun y =>
      c = crossIntermediateComponent G hfree hde x y
    let L₁ := R.filter fun y =>
      c = crossIntermediateComponent G hfree hef₁ y z₁
    let L₂ := R.filter fun y =>
      c = crossIntermediateComponent G hfree hef₂ y z₂
    (L₁ ∩ L₂).Nonempty ∨ L₁ ∪ L₂ = R := by
  classical
  let R := (Finset.univ : Finset e.supp).filter fun y =>
    c = crossIntermediateComponent G hfree hde x y
  let L₁ := R.filter fun y =>
    c = crossIntermediateComponent G hfree hef₁ y z₁
  let L₂ := R.filter fun y =>
    c = crossIntermediateComponent G hfree hef₂ y z₂
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hRcard : R.card = 4 := by
    dsimp [R]
    exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d c e hde
        (by simpa using hall d) (by simpa using hall c)
        (by simpa using hall e) x
  have hL₁card : L₁.card = 2 := by
    have h := hallTwo d c e f₁ hde hef₁ hdf₁ x z₁ hdirect₁
    simpa only [L₁, R, Finset.filter_filter, and_assoc] using h
  have hL₂card : L₂.card = 2 := by
    have h := hallTwo d c e f₂ hde hef₂ hdf₂ x z₂ hdirect₂
    simpa only [L₂, R, Finset.filter_filter, and_assoc] using h
  by_cases hinter : (L₁ ∩ L₂).Nonempty
  · exact Or.inl hinter
  · right
    have hinterEmpty : L₁ ∩ L₂ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hinter
    have hdisjoint : Disjoint L₁ L₂ := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hinterEmpty
    have hunionCard : (L₁ ∪ L₂).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisjoint, hL₁card, hL₂card]
    have hsub : L₁ ∪ L₂ ⊆ R := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.filter_subset _ _ hy
      · exact Finset.filter_subset _ _ hy
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hunionCard, hRcard])

end

end Erdos85
