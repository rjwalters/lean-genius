import Proofs.Erdos85SizeTwoMuNegThreeEightEightSignedParameterConsumer
import Proofs.Erdos85SizeTwoMuNegOneEightEightSignedRegularity

/-! # Concrete signed parameter for the `mu=-1` eight-plus-eight split -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1200000 in
/-- A single `k≤3` controls the signed defect distribution of both internal
eight-cycles: diagonal same-sign degree is `k`, and cross same-sign degree is
`3-k` in both directions. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
    ∃ k : ℕ, k ≤ 3 ∧
      (∀ x ∈ A,
        (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = k) ∧
      (∀ x ∈ B,
        (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = k) ∧
      (∀ x ∈ A,
        (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = 3 - k) ∧
      (∀ x ∈ B,
        (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = 3 - k) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨ha8, hb8, _r, _hr2, _hr7, _haa, _habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hAcard : A.card = 8 := by
    have heq : A = a.supp.toFinite.toFinset := by ext x; simp [A]
    rw [heq, ← Set.ncard_eq_toFinset_card, ha8]
  have hBcard : B.card = 8 := by
    have heq : B = b.supp.toFinite.toFinset := by ext x; simp [B]
    rw [heq, ← Set.ncard_eq_toFinset_card, hb8]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hxa' := (Finset.mem_filter.mp hxa).2
    have hxb' := (Finset.mem_filter.mp hxb).2
    exact hab <| (ConnectedComponent.mem_supp_iff a x).mp hxa' |>.symm.trans
      ((ConnectedComponent.mem_supp_iff b x).mp hxb')
  have hcover : A ∪ B = (Finset.univ : Finset c.supp) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard,
      Finset.card_univ]
    have hsuppcard : Fintype.card c.supp = 16 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hc]
    omega
  have hprofile := orderSixtyFour_sizeTwo_muNegOne_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  have hglobal : ∀ x ∈ A ∪ B,
      ((K.neighborFinset x).filter fun y ↦ s y.1 = s x.1).card = 3 := by
    intro x _hx
    let D := secondOrderDefectGraph G
    have himage (t : ℤ) : Finset.image Subtype.val
        ((K.neighborFinset x).filter fun y ↦ s y.1 = t) =
        (D.neighborFinset x.1).filter fun y ↦ s y = t := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨z, ⟨hK, hsz⟩, rfl⟩
        exact ⟨hK, hsz⟩
      · rintro ⟨hDy, hsy⟩
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c y]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDy).symm.trans
            ((ConnectedComponent.mem_supp_iff c x.1).mp x.2)
        exact ⟨⟨y, hyc⟩, ⟨hDy, hsy⟩, rfl⟩
    rcases hs_in x.1 x.2 with hsx | hsx
    · have hp := (hprofile.2.2 x.1 x.2).2 hsx
      calc
        _ = ((D.neighborFinset x.1).filter fun y ↦ s y = -1).card := by
          rw [← congrArg Finset.card (himage (-1)),
            Finset.card_image_of_injective _ Subtype.val_injective]
          simp [hsx]
        _ = 3 := hp.2.2.1
    · have hp := (hprofile.2.2 x.1 x.2).1 hsx
      calc
        _ = ((D.neighborFinset x.1).filter fun y ↦ s y = 1).card := by
          rw [← congrArg Finset.card (himage 1),
            Finset.card_image_of_injective _ Subtype.val_injective]
          simp [hsx]
        _ = 3 := hp.2.2.1
  have hregular := orderSixtyFour_sizeTwo_muNegOne_eightEight_internalSame_regular
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by rw [hAcard]; omega : 0 < A.card)
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp (by rw [hBcard]; omega : 0 < B.card)
  let ka := (A.filter fun y ↦ K.Adj x₀ y ∧ s y.1 = s x₀.1).card
  let kb := (B.filter fun y ↦ K.Adj y₀ y ∧ s y.1 = s y₀.1).card
  have hA : ∀ x ∈ A,
      (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = ka := by
    intro x hx
    have hxa := (Finset.mem_filter.mp hx).2
    have hx₀a := (Finset.mem_filter.mp hx₀).2
    have hxcard := component_sameSign_filter_card_eq_induce H K a
      (fun z : c.supp ↦ s z.1) x hxa
    have hx₀card := component_sameSign_filter_card_eq_induce H K a
      (fun z : c.supp ↦ s z.1) x₀ hx₀a
    simpa [A, ka] using hxcard.trans
      ((hregular.1 ⟨x, hxa⟩ ⟨x₀, hx₀a⟩).trans hx₀card.symm)
  have hB : ∀ x ∈ B,
      (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = kb := by
    intro x hx
    have hxb := (Finset.mem_filter.mp hx).2
    have hy₀b := (Finset.mem_filter.mp hy₀).2
    have hxcard := component_sameSign_filter_card_eq_induce H K b
      (fun z : c.supp ↦ s z.1) x hxb
    have hy₀card := component_sameSign_filter_card_eq_induce H K b
      (fun z : c.supp ↦ s z.1) y₀ hy₀b
    simpa [B, kb] using hxcard.trans
      ((hregular.2 ⟨x, hxb⟩ ⟨y₀, hy₀b⟩).trans hy₀card.symm)
  have hk := equal_bipartition_internalSame_constants_eq K
    (fun z : c.supp ↦ s z.1) A B hcover hdisj
      (by omega) (by omega) 3 ka kb hglobal hA hB
  refine ⟨ka, ?_, hA, ?_, hk.2.1, ?_⟩
  · obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hAcard]; omega : 0 < A.card)
    have hg := hglobal x (Finset.mem_union_left B hx)
    have hi := hA x hx
    have hsub : (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1) ⊆
        (K.neighborFinset x).filter fun y ↦ s y.1 = s x.1 := by
      intro y hy
      have hy' := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨(K.mem_neighborFinset x y).mpr hy'.2.1,
        hy'.2.2⟩
    rw [← hi, ← hg]
    exact Finset.card_le_card hsub
  · intro x hx
    exact (hB x hx).trans hk.1.symm
  · intro x hx
    exact (hk.2.2 x hx).trans (congrArg (3 - ·) hk.1).symm

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
