import Proofs.Erdos85OrderSixtyFourRoutingLiftPairDichotomy

/-! # Exact overlap trichotomy for paired routing lifts -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- Two exact two-lift fibers in one four-point routing row either share
exactly one hub, coincide, or are disjoint and partition the row. -/
theorem orderSixtyFour_twoClosingRoutes_lift_inter_card_one_or_eq_or_union_eq_row
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
    (L₁ ∩ L₂).card = 1 ∨ L₁ = L₂ ∨ L₁ ∪ L₂ = R := by
  classical
  let R := (Finset.univ : Finset e.supp).filter fun y =>
    c = crossIntermediateComponent G hfree hde x y
  let L₁ := R.filter fun y =>
    c = crossIntermediateComponent G hfree hef₁ y z₁
  let L₂ := R.filter fun y =>
    c = crossIntermediateComponent G hfree hef₂ y z₂
  have hL₁card : L₁.card = 2 := by
    have h := hallTwo d c e f₁ hde hef₁ hdf₁ x z₁ hdirect₁
    simpa only [L₁, R, Finset.filter_filter, and_assoc] using h
  have hL₂card : L₂.card = 2 := by
    have h := hallTwo d c e f₂ hde hef₂ hdf₂ x z₂ hdirect₂
    simpa only [L₂, R, Finset.filter_filter, and_assoc] using h
  rcases orderSixtyFour_twoClosingRoutes_lift_inter_nonempty_or_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hdirect₁ hdirect₂ hallTwo with hinter | hunion
  · have hpos : 0 < (L₁ ∩ L₂).card := Finset.card_pos.mpr hinter
    have hle : (L₁ ∩ L₂).card ≤ 2 := by
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hL₁card
    by_cases hone : (L₁ ∩ L₂).card = 1
    · exact Or.inl hone
    · right
      left
      have hcardTwo : (L₁ ∩ L₂).card = 2 := by omega
      have heq₁ : L₁ ∩ L₂ = L₁ :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
          rw [hcardTwo, hL₁card])
      have heq₂ : L₁ ∩ L₂ = L₂ :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
          rw [hcardTwo, hL₂card])
      exact heq₁.symm.trans heq₂
  · exact Or.inr (Or.inr hunion)

end

end Erdos85
