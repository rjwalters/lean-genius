import Proofs.Erdos85SizeTwoMuNegFiveNeutralProjection

/-! # The `mu=-5` neutral projection is the cross-defect complement -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An opposite-sign shore pair has a neutral exterior common neighbor
exactly when it is not a second-order defect edge. -/
theorem orderSixtyFour_sizeTwo_muNegFive_neutralProjection_iff_not_defect
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
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
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
    let N := MuNegFiveNeutralProjection G c s
    ∀ x : Xp, ∀ y : Xm, N x y ↔ ¬ D.Adj x.1 y.1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let N := MuNegFiveNeutralProjection G c s
  have hregular :=
    orderSixtyFour_sizeTwo_muNegFive_neutralProjection_biregular
      G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hprofile := orderSixtyFour_sizeTwo_muNegFive_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hXmCard : Fintype.card Xm = 8 := by
    let T := (Finset.univ : Finset V).filter fun y => y ∈ c.supp ∧ s y = -1
    let e : Xm ≃ {y : V // y ∈ T} :=
      Equiv.subtypeEquivRight fun y => by simp [T, D]
    calc
      Fintype.card Xm = Fintype.card {y : V // y ∈ T} := Fintype.card_congr e
      _ = T.card := Fintype.card_coe T
      _ = 8 := hprofile.2.1
  intro x
  let NR := (Finset.univ : Finset Xm).filter fun y => N x y
  let DR := (Finset.univ : Finset Xm).filter fun y => D.Adj x.1 y.1
  let CR := (Finset.univ : Finset Xm).filter fun y => ¬ D.Adj x.1 y.1
  have hNRcard : NR.card = 2 := hregular.1 x
  have hDRcard : DR.card = 6 := by
    let T := (D.neighborFinset x.1).filter fun y => s y = -1
    have himage : Finset.image Subtype.val DR = T := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, DR, T]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(D.mem_neighborFinset _ _).mpr hz, z.2.2⟩
      · rintro ⟨hxy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            ((D.mem_neighborFinset _ _).mp hxy)).symm.trans x.2.1
        exact ⟨⟨y, hyc, hsy⟩, (D.mem_neighborFinset _ _).mp hxy, rfl⟩
    calc
      DR.card = (Finset.image Subtype.val DR).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = T.card := congrArg Finset.card himage
      _ = 6 := (hprofile.2.2 x.1 x.2.1).1 x.2.2 |>.2.2.2
  have hCRcard : CR.card = 2 := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset Xm)) (p := fun y => D.Adj x.1 y.1)
    change DR.card + CR.card = (Finset.univ : Finset Xm).card at hsplit
    rw [hDRcard, Finset.card_univ, hXmCard] at hsplit
    omega
  have hsub : NR ⊆ CR := by
    intro y hy
    have hNxy := (Finset.mem_filter.mp hy).2
    obtain ⟨z, hxz, hyz⟩ := hNxy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree
      (fun h => by
        have hsxy := congrArg s h
        rw [x.2.2, y.2.2] at hsxy
        omega) hxz hyz
  have heq : NR = CR := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro y
  constructor
  · intro hxy
    have hmemNR : y ∈ NR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    have hmemCR : y ∈ CR := by rw [← heq]; exact hmemNR
    exact (Finset.mem_filter.mp hmemCR).2
  · intro hxy
    have hmemCR : y ∈ CR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
    have hmemNR : y ∈ NR := by rw [heq]; exact hmemCR
    exact (Finset.mem_filter.mp hmemNR).2

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_neutralProjection_iff_not_defect
