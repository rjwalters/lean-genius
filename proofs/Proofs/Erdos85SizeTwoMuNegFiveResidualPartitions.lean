import Proofs.Erdos85SizeTwoMuNegFiveResidualTwoFactors
import Proofs.Erdos85OrderEightTwoRegularComponentSizes

/-! # Cycle partitions of the `mu=-5` residual two-factors -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

def OrderEightTwoFactorPartition {X : Type*} [Fintype X]
    (H : SimpleGraph X) : Prop :=
  (Nat.card H.ConnectedComponent = 1 ∧
    ∀ c : H.ConnectedComponent, c.supp.ncard = 8) ∨
  (Nat.card H.ConnectedComponent = 2 ∧
    ∀ c d : H.ConnectedComponent, c ≠ d →
      (c.supp.ncard = 3 ∧ d.supp.ncard = 5) ∨
      (c.supp.ncard = 4 ∧ d.supp.ncard = 4) ∨
      (c.supp.ncard = 5 ∧ d.supp.ncard = 3))

theorem orderSixtyFour_sizeTwo_muNegFive_residual_partitions
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
      OrderEightTwoFactorPartition
        ((twoIncidenceShadow Rp ⊔
          freeInvolutionMatchingGraph fp hfpinv hfpne)ᶜ) ∧
      OrderEightTwoFactorPartition
        ((twoIncidenceShadow Rm ⊔
          freeInvolutionMatchingGraph fm hfminv hfmne)ᶜ) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let Sp := MuNegFiveExtremeFiber G c s 2
  let Sm := MuNegFiveExtremeFiber G c s (-2)
  let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
  let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
  obtain ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne,
      hfp, hfm, hdegP, hdegM⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_residual_twoFactors
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
  have hp := twoRegular_orderEight_component_partition HP hXpCard hdegP
  have hm := twoRegular_orderEight_component_partition HM hXmCard hdegM
  refine ⟨fp, fm, hfpinv, hfpne, hfminv, hfmne, hfp, hfm, ?_, ?_⟩
  · change OrderEightTwoFactorPartition HP
    simpa [OrderEightTwoFactorPartition, Nat.card_eq_fintype_card] using hp
  · change OrderEightTwoFactorPartition HM
    simpa [OrderEightTwoFactorPartition, Nat.card_eq_fintype_card] using hm

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_residual_partitions
