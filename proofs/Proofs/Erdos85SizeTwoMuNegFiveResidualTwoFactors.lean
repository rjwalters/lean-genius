import Proofs.Erdos85FreeMatchingRegularResidual
import Proofs.Erdos85SizeTwoMuNegFiveShadowMatchingDisjoint

/-!
# Residual two-factors at `mu=-5`

Each sign shore carries a defect perfect matching and a disjoint
four-regular exterior shadow.  Their unused pairs form a two-regular graph
on the eight-point shore.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_residual_twoFactors
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
      (∀ x y, D.Adj x.1 y.1 ↔ fp x = y) ∧
      (∀ x y, D.Adj x.1 y.1 ↔ fm x = y) ∧
      (∀ x, ((twoIncidenceShadow Rp ⊔
        freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ).degree x = 2) ∧
      (∀ x, ((twoIncidenceShadow Rm ⊔
        freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ).degree x = 2) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let Sp := MuNegFiveExtremeFiber G c s 2
  let Sm := MuNegFiveExtremeFiber G c s (-2)
  let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
  let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
  obtain ⟨fp, fm, hfp, hfpinv, hfpne, hfm, hfminv, hfmne⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_sameSign_defect_matchings
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hshadow := orderSixtyFour_sizeTwo_muNegFive_extreme_shadows_fourRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hdisj := orderSixtyFour_sizeTwo_muNegFive_extreme_shadows_disjoint_defect
    G hfree c s
  have hprofile := orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hXpCard : Fintype.card Xp = 8 := by
    let S := (Finset.univ : Finset V).filter fun x => x ∈ c.supp ∧ s x = 1
    let e : Xp ≃ {x : V // x ∈ S} :=
      Equiv.subtypeEquivRight fun x => by simp [S, D]
    calc
      Fintype.card Xp = Fintype.card {x : V // x ∈ S} := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = 8 := hprofile.1
  have hXmCard : Fintype.card Xm = 8 := by
    let S := (Finset.univ : Finset V).filter fun x => x ∈ c.supp ∧ s x = -1
    let e : Xm ≃ {x : V // x ∈ S} :=
      Equiv.subtypeEquivRight fun x => by simp [S, D]
    calc
      Fintype.card Xm = Fintype.card {x : V // x ∈ S} := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = 8 := hprofile.2.1
  have hdisjP : ∀ ⦃x y⦄, (twoIncidenceShadow Rp).Adj x y → fp x ≠ y := by
    intro x y hxy heq
    exact hdisj.1 hxy ((hfp x y).mpr heq)
  have hdisjM : ∀ ⦃x y⦄, (twoIncidenceShadow Rm).Adj x y → fm x ≠ y := by
    intro x y hxy heq
    exact hdisj.2 hxy ((hfm x y).mpr heq)
  have hresP := fourRegular_disjoint_freeMatching_residual_twoRegular
    hXpCard (twoIncidenceShadow Rp) hshadow.1 fp hfpinv hfpne hdisjP
  have hresM := fourRegular_disjoint_freeMatching_residual_twoRegular
    hXmCard (twoIncidenceShadow Rm) hshadow.2 fm hfminv hfmne hdisjM
  refine ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, hfp, hfm, ?_, ?_⟩
  · exact hresP
  · exact hresM

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_residual_twoFactors
