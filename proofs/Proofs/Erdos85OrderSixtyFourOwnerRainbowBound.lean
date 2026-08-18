import Proofs.Erdos85BinarySquareRoutingRainbowEquiv
import Proofs.Erdos85OrderSixtyFourRoutingRainbowExcess

/-! # Quantitative owner-rainbow bounds at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For fixed ordered endpoint/route/intermediate colors, there are at most
128 ordered owner rainbows.  Exactly 64 endpoint pairs have the prescribed
direct routing color, and each has at most two rainbow excess completions. -/
theorem orderSixtyFour_ownerRainbowTriples_card_le_128
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    Fintype.card (ownerRainbowTriples G d e f c) ≤ 128 := by
  classical
  let T := routingRainbowEndpointTriples G hfree c d e f hce hef hcf
  let S : Finset T := Finset.univ
  let π : T → c.supp × f.supp := fun r => (r.1.1, r.1.2.2)
  have hfiber : ∀ a ∈ S.image π,
      (S.filter fun r => π r = a).card ≤ 2 := by
    rintro ⟨x, w⟩ ha
    obtain ⟨r₀, _hr₀S, hr₀π⟩ := Finset.mem_image.mp ha
    have hx₀ : r₀.1.1 = x := by
      simpa [π] using congrArg Prod.fst hr₀π
    have hw₀ : r₀.1.2.2 = w := by
      simpa [π] using congrArg Prod.snd hr₀π
    have hr₀route := r₀.2.2.2.1
    have hxwRoute : crossIntermediateComponent G hfree hcf x w = d := by
      rw [← hx₀, ← hw₀]
      exact hr₀route
    let E := orderSixtyFourDefectComponentEquivFinFour G hcount
    let k : Fin 4 := E d
    have hxwArray : orderSixtyFourRoutingArray G hfree hcount hcf x w = k := by
      change E (crossIntermediateComponent G hfree hcf x w) = E d
      rw [hxwRoute]
    let R := orderSixtyFourRoutingRainbowExcessFinset
      G hfree hcount hce hef hcf k x w
    have hRle : R.card ≤ 2 := by
      exact orderSixtyFourRoutingRainbowExcess_card_le_two
        G hfree hreg hcount hce hef hcf k x w hxwArray
    refine (Finset.card_le_card_of_injOn (fun r : T => r.1.2.1) ?_ ?_).trans hRle
    · intro r hr
      have hrπ := (Finset.mem_filter.mp hr).2
      have hx := congrArg Prod.fst hrπ
      have hw := congrArg Prod.snd hrπ
      have hr₁ := r.2.1
      have hr₂ := r.2.2.1
      have hrainbow := r.2.2.2.2
      have hxr : r.1.1 = x := by
        simpa [π] using congrArg Prod.fst hrπ
      have hwr : r.1.2.2 = w := by
        simpa [π] using congrArg Prod.snd hrπ
      have hcomp₁ : orderSixtyFourRoutingArray G hfree hcount hce x r.1.2.1 = k := by
        change E (crossIntermediateComponent G hfree hce x r.1.2.1) = E d
        rw [← hxr, hr₁]
      have hcomp₂ : orderSixtyFourRoutingArray G hfree hcount hef r.1.2.1 w = k := by
        change E (crossIntermediateComponent G hfree hef r.1.2.1 w) = E d
        rw [← hwr, hr₂]
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hcomp₁, hcomp₂⟩
      · simpa only [hxr, hwr] using hrainbow
    · intro r₁ hr₁ r₂ hr₂ hz
      have hp₁ := (Finset.mem_filter.mp hr₁).2
      have hp₂ := (Finset.mem_filter.mp hr₂).2
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg Prod.fst hp₁).trans (congrArg Prod.fst hp₂).symm
      · apply Prod.ext
        · exact hz
        · exact (congrArg Prod.snd hp₁).trans (congrArg Prod.snd hp₂).symm
  have htotal : S.card ≤ 2 * (S.image π).card :=
    Finset.card_le_mul_card_image S 2 hfiber
  let P := ((Finset.univ : Finset c.supp) ×ˢ
    (Finset.univ : Finset f.supp)).filter fun p =>
      crossIntermediateComponent G hfree hcf p.1 p.2 = d
  have himageSub : S.image π ⊆ P := by
    intro a ha
    obtain ⟨r, _hrS, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      r.2.2.2.1⟩
  have hPcard : P.card = 64 := by
    have hmaps : ∀ p ∈ P, p.1 ∈ (Finset.univ : Finset c.supp) := by
      intro p _hp
      exact Finset.mem_univ _
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      (Finset.univ : Finset c.supp).sum
          (fun x => (P.filter fun p => p.1 = x).card) =
          (Finset.univ : Finset c.supp).sum (fun _ => 4) := by
        apply Finset.sum_congr rfl
        intro x _hx
        have hrow := orderSixtyFourRoutingArray_row_color_card_eq_four
          G hfree hreg hcount hcf x
            (orderSixtyFourDefectComponentEquivFinFour G hcount d)
        let Q := (Finset.univ : Finset f.supp).filter fun w =>
          crossIntermediateComponent G hfree hcf x w = d
        have hcardEq : (P.filter fun p => p.1 = x).card = Q.card := by
          apply Finset.card_bij (fun p _hp => p.2)
          · intro p hp
            have hp' := Finset.mem_filter.mp hp
            have hpP := Finset.mem_filter.mp hp'.1
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ _, hp'.2 ▸ hpP.2⟩
          · intro p₁ hp₁ p₂ hp₂ heq
            have h₁ := (Finset.mem_filter.mp hp₁).2
            have h₂ := (Finset.mem_filter.mp hp₂).2
            exact Prod.ext (h₁.trans h₂.symm) heq
          · intro w hw
            have hw' := Finset.mem_filter.mp hw
            refine ⟨(x, w), ?_, rfl⟩
            apply Finset.mem_filter.mpr
            refine ⟨?_, rfl⟩
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr
              ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hw'.2⟩
        rw [hcardEq]
        simpa [Q, orderSixtyFourRoutingArray] using hrow
      _ = 16 * 4 := by
        have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
          G hfree hreg hcount
        have hc : Fintype.card c.supp = 16 := by
          rw [show Fintype.card c.supp = c.supp.ncard by
            simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp]
          exact hall c
        rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, hc]
      _ = 64 := by norm_num
  have himage : (S.image π).card ≤ 64 := by
    exact (Finset.card_le_card himageSub).trans_eq hPcard
  have hroute : Fintype.card T ≤ 128 := by
    change S.card ≤ 128
    omega
  rw [routingRainbowEndpointTriples_card_eq_ownerRainbowTriples_card
    G hfree c d e f hce hef hcf] at hroute
  exact hroute

end

end Erdos85
