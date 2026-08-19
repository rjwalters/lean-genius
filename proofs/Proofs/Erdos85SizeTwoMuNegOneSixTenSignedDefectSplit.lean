import Proofs.Erdos85SizeTwoMuNegThreeSixTenShortCensus
import Proofs.Erdos85SizeTwoMuNegOneInternalStructure

/-! # Signed defect split from the short cycle in the `mu=-1` stratum -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At every vertex of a short six-cycle, its two defect neighbors on that
cycle have opposite sign. The five defect neighbors off the short cycle split
as exactly three of the same sign and two of the opposite sign. -/
theorem orderSixtyFour_sizeTwo_muNegOne_sixTen_short_signedDefectSplit
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
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    ∀ x : c.supp, x ∈ a.supp →
      let A := componentNeighborFinset K H a x
      let O := (K.neighborFinset x).filter fun y ↦ y ∉ a.supp
      ((A.filter fun y ↦ s y.1 = s x.1).card = 0) ∧
      ((A.filter fun y ↦ s y.1 = -s x.1).card = 2) ∧
      ((O.filter fun y ↦ s y.1 = s x.1).card = 3) ∧
      ((O.filter fun y ↦ s y.1 = -s x.1).card = 2) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := G.induce c.supp
  let K := D.induce c.supp
  have hAeq := orderSixtyFour_sizeTwo_sixTen_shortCycle_census_of_filtered
    G hfree hreg hcard c hc s hs_out hs_in hH a b ha hb |>.2
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hprofile := orderSixtyFour_sizeTwo_muNegOne_signed_internal_degreeProfile
    G hfree hreg hcard c hc s hs_out hs_in hH hD
  intro x hx
  let A := componentNeighborFinset K H a x
  let O := (K.neighborFinset x).filter fun y ↦ y ∉ a.supp
  have hAH : A = H.neighborFinset x := by
    ext y
    simp only [A, componentNeighborFinset, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hKxy, hya⟩
      have hy : y ∈ a.supp := (ConnectedComponent.mem_supp_iff a y).mpr hya
      exact (hAeq x y hx hy).mp hKxy
    · intro hHxy
      have hy : y ∈ a.supp := by
        rw [ConnectedComponent.mem_supp_iff a y]
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj hHxy).symm.trans
          ((ConnectedComponent.mem_supp_iff a x).mp hx)
      exact ⟨(hAeq x y hx hy).mpr hHxy,
        (ConnectedComponent.mem_supp_iff a y).mp hy⟩
  have hAcard : A.card = 2 := by
    rw [hAH, H.card_neighborFinset_eq_degree]
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) x
  have hAopp : ∀ y ∈ A, s y.1 = -s x.1 := by
    intro y hy
    have hHxy : H.Adj x y := by
      rw [hAH] at hy
      exact (H.mem_neighborFinset x y).mp hy
    have hymem : y.1 ∈ componentNeighborFinset G D c x.1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hHxy,
        (ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull x.2).2 y.1 hymem
  have hAsameCard : (A.filter fun y ↦ s y.1 = s x.1).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    have hy' := Finset.mem_filter.mp hy
    have hsx := hs_in x.1 x.2
    have hopp := hAopp y hy'.1
    rcases hsx with hsx | hsx <;> omega
  have hAoppCard : (A.filter fun y ↦ s y.1 = -s x.1).card = 2 := by
    rw [Finset.filter_eq_self.mpr hAopp, hAcard]
  have hAO : A ∪ O = K.neighborFinset x := by
    ext y
    simp only [Finset.mem_union, A, O, componentNeighborFinset,
      Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (⟨hxy, -⟩ | ⟨hxy, -⟩) <;> exact hxy
    · intro hxy
      by_cases hya : y ∈ a.supp
      · exact Or.inl ⟨hxy, (ConnectedComponent.mem_supp_iff a y).mp hya⟩
      · exact Or.inr ⟨hxy, hya⟩
  have hdisj : Disjoint A O := by
    rw [Finset.disjoint_left]
    intro y hyA hyO
    exact (Finset.mem_filter.mp hyO).2
      ((ConnectedComponent.mem_supp_iff a y).mpr
        (Finset.mem_filter.mp hyA).2)
  have hKsigned :
      ((K.neighborFinset x).filter fun y ↦ s y.1 = s x.1).card = 3 ∧
      ((K.neighborFinset x).filter fun y ↦ s y.1 = -s x.1).card = 4 := by
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
      constructor
      · calc
          _ = ((D.neighborFinset x.1).filter fun y ↦ s y = -1).card := by
            rw [← congrArg Finset.card (himage (-1)),
              Finset.card_image_of_injective _ Subtype.val_injective]
            simp [hsx]
          _ = 3 := hp.2.2.1
      · calc
          _ = ((D.neighborFinset x.1).filter fun y ↦ s y = 1).card := by
            rw [← congrArg Finset.card (himage 1),
              Finset.card_image_of_injective _ Subtype.val_injective]
            simp [hsx]
          _ = 4 := hp.2.2.2
    · have hp := (hprofile.2.2 x.1 x.2).1 hsx
      constructor
      · calc
          _ = ((D.neighborFinset x.1).filter fun y ↦ s y = 1).card := by
            rw [← congrArg Finset.card (himage 1),
              Finset.card_image_of_injective _ Subtype.val_injective]
            simp [hsx]
          _ = 3 := hp.2.2.1
      · calc
          _ = ((D.neighborFinset x.1).filter fun y ↦ s y = -1).card := by
            rw [← congrArg Finset.card (himage (-1)),
              Finset.card_image_of_injective _ Subtype.val_injective]
            simp [hsx]
          _ = 4 := hp.2.2.2
  refine ⟨hAsameCard, hAoppCard, ?_, ?_⟩
  · have hfilterUnion :
        (K.neighborFinset x).filter (fun y ↦ s y.1 = s x.1) =
          (A.filter fun y ↦ s y.1 = s x.1) ∪
            (O.filter fun y ↦ s y.1 = s x.1) := by
      rw [← Finset.filter_union, hAO]
    have hs := hKsigned.1
    rw [hfilterUnion, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), hAsameCard, zero_add] at hs
    exact hs
  · have hfilterUnion :
        (K.neighborFinset x).filter (fun y ↦ s y.1 = -s x.1) =
          (A.filter fun y ↦ s y.1 = -s x.1) ∪
            (O.filter fun y ↦ s y.1 = -s x.1) := by
      rw [← Finset.filter_union, hAO]
    have hs := hKsigned.2
    rw [hfilterUnion, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), hAoppCard] at hs
    change (O.filter fun y ↦ s y.1 = -s x.1).card = 2
    omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_sixTen_short_signedDefectSplit
