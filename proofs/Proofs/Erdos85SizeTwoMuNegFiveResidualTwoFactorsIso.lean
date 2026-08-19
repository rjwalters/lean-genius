import Proofs.Erdos85SizeTwoMuNegFiveResidualEqualsInternalShadow
import Proofs.Erdos85SizeTwoMuNegFiveResidualShadowIso

/-! # The two `mu=-5` residual two-factors are isomorphic -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_residual_twoFactors_iso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (-5 : ℤ) * s z) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let Sp := MuNegFiveExtremeFiber G c s 2
    let Sm := MuNegFiveExtremeFiber G c s (-2)
    let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
    let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
    ∃ fp : Equiv.Perm Xp, ∃ fm : Equiv.Perm Xm,
      ∃ hfpinv : ∀ x, fp (fp x) = x, ∃ hfpne : ∀ x, fp x ≠ x,
      ∃ hfminv : ∀ x, fm (fm x) = x, ∃ hfmne : ∀ x, fm x ≠ x,
      Nonempty
        (((twoIncidenceShadow Rp ⊔
            freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ) ≃g
          ((twoIncidenceShadow Rm ⊔
            freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ)) := by
  classical
  dsimp only
  obtain ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, hP, hM⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_residual_eq_internal_shadows
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  obtain ⟨E⟩ := orderSixtyFour_sizeTwo_muNegFive_internal_shadows_iso
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  refine ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, ?_⟩
  rw [← hP, ← hM]
  exact ⟨E⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_residual_twoFactors_iso
