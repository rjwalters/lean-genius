import Proofs.Erdos85SizeTwoMuNegFiveResidualPartitions
import Proofs.Erdos85SizeTwoMuNegFiveResidualTwoFactorsIso

/-! # Coherent synchronized residual package at `mu=-5`

The partition and isomorphism conclusions are packaged around the same
chosen shore matchings, avoiding any mismatch between independent
existential witnesses.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_synchronized_residual_package
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
      let HP := (twoIncidenceShadow Rp ⊔
        freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ
      let HM := (twoIncidenceShadow Rm ⊔
        freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ
      ∃ E : HP ≃g HM,
        OrderEightTwoFactorPartition HP ∧
        OrderEightTwoFactorPartition HM ∧
        ∀ C : HP.ConnectedComponent,
          C.supp.ncard = (E.connectedComponentEquiv C).supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let Sp := MuNegFiveExtremeFiber G c s 2
  let Sm := MuNegFiveExtremeFiber G c s (-2)
  let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
  let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
  let B := fun x : Xp => fun y : Xm => G.Adj x.1 y.1
  obtain ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, hP, hM⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_residual_eq_internal_shadows
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  obtain ⟨E⟩ := orderSixtyFour_sizeTwo_muNegFive_internal_shadows_iso
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hint := orderSixtyFour_sizeTwo_muNegFive_internal_shadows_twoRegular
    G hfree hreg hcard c hc s hs_out hs_in hH hD
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
  let HP := (twoIncidenceShadow Rp ⊔
    freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ
  let HM := (twoIncidenceShadow Rm ⊔
    freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ
  have hdegP : ∀ x, HP.degree x = 2 := by
    intro x
    have hN := congrArg (fun K : SimpleGraph Xp => K.neighborSet x) hP
    calc
      HP.degree x = Fintype.card (HP.neighborSet x) :=
        (HP.card_neighborSet_eq_degree x).symm
      _ = Fintype.card ((twoIncidenceShadow B).neighborSet x) :=
        Fintype.card_congr (Equiv.setCongr hN.symm)
      _ = (twoIncidenceShadow B).degree x :=
        (twoIncidenceShadow B).card_neighborSet_eq_degree x
      _ = 2 := hint.1 x
  have hdegM : ∀ x, HM.degree x = 2 := by
    intro x
    have hN := congrArg (fun K : SimpleGraph Xm => K.neighborSet x) hM
    calc
      HM.degree x = Fintype.card (HM.neighborSet x) :=
        (HM.card_neighborSet_eq_degree x).symm
      _ = Fintype.card
          ((twoIncidenceShadow (fun z x => B x z)).neighborSet x) :=
        Fintype.card_congr (Equiv.setCongr hN.symm)
      _ = (twoIncidenceShadow (fun z x => B x z)).degree x :=
        (twoIncidenceShadow (fun z x => B x z)).card_neighborSet_eq_degree x
      _ = 2 := hint.2 x
  have hp := twoRegular_orderEight_component_partition HP hXpCard hdegP
  have hm := twoRegular_orderEight_component_partition HM hXmCard hdegM
  have E' : HP ≃g HM := by
    change ((twoIncidenceShadow Rp ⊔
      freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ) ≃g
      ((twoIncidenceShadow Rm ⊔
        freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ)
    rw [← hP, ← hM]
    exact E
  refine ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, E', ?_, ?_, ?_⟩
  · change OrderEightTwoFactorPartition HP
    simpa [OrderEightTwoFactorPartition, Nat.card_eq_fintype_card] using hp
  · change OrderEightTwoFactorPartition HM
    simpa [OrderEightTwoFactorPartition, Nat.card_eq_fintype_card] using hm
  · intro C
    exact Set.ncard_congr' (ConnectedComponent.isoEquivSupp E' C)

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_synchronized_residual_package
