import Proofs.Erdos85SizeTwoMuNegThreeEightEightAntipodalDegree

/-! # The top signed-capacity endpoint in the `mu=-3` C8+C8 branch -/

namespace Erdos85

noncomputable section

/-- At signed capacity `r+k=6`, every vertex on the chosen C8 shore has
antipodal degree seven and no triangle-free incident edge. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_capacitySix_allTriangle
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
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    ∃ k r : ℕ, k ≤ 2 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      (r + k = 6 → ∀ x : c.supp, x ∈ a.supp →
        (antipodalGraph G).degree x.1 = 7 ∧
        (triangleFreeEdgeGraph G).degree x.1 = 0) := by
  obtain ⟨k, r, hk, hr2, hr7, hsub⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signed_antipodal_subdegree
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  refine ⟨k, r, hk, hr2, hr7, ?_⟩
  intro hcap x hxa
  obtain ⟨hle, hdeg5 | hdeg7⟩ := hsub x hxa
  · omega
  · refine ⟨hdeg7, ?_⟩
    have htf := binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree (q := 8) (by omega) (by decide) hreg hcard c hc x
    rcases htf with hzero | htwo
    · exact hzero
    · have hcard64 : Fintype.card V = 8 * (8 - 1) + 3 + 5 := by
        norm_num at hcard ⊢
        exact hcard
      have hanti := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
        G hfree (d := 8) (e := 5) (by omega) hreg hcard64 x.1
      have htfcard : (triangleFreeNeighbors G x.1).card =
          (triangleFreeEdgeGraph G).degree x.1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
      rw [htfcard, htwo, hdeg7] at hanti
      omega

set_option maxHeartbeats 1200000 in
/-- At signed capacity six, both C8 shores are all-triangle sectors for the
same quotient parameters. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_capacitySix_bothAllTriangle
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
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    ∃ k r : ℕ, k ≤ 2 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      (r + k = 6 →
        (∀ x : c.supp, x ∈ a.supp →
          (antipodalGraph G).degree x.1 = 7 ∧
          (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
        (∀ x : c.supp, x ∈ b.supp →
          (antipodalGraph G).degree x.1 = 7 ∧
          (triangleFreeEdgeGraph G).degree x.1 = 0)) := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨k, hk, hA, hB, _hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨r, hr2, hr7, hcrossA, hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_crossAntipodal_degree
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hxa' := (Finset.mem_filter.mp hxa).2
    have hxb' := (Finset.mem_filter.mp hxb).2
    exact hab <| (SimpleGraph.ConnectedComponent.mem_supp_iff a x).mp hxa' |>.symm.trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff b x).mp hxb')
  have hfinish (x : c.supp)
      (hle : 6 ≤ (antipodalGraph G).degree x.1) :
      (antipodalGraph G).degree x.1 = 7 ∧
        (triangleFreeEdgeGraph G).degree x.1 = 0 := by
    have hdeg := orderSixtyFour_sizeTwo_antipodal_degree_eq_five_or_seven
      G hfree hreg hcard c hc x
    have hdeg7 : (antipodalGraph G).degree x.1 = 7 := by omega
    refine ⟨hdeg7, ?_⟩
    have htf := binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree (q := 8) (by omega) (by decide) hreg hcard c hc x
    rcases htf with hzero | htwo
    · exact hzero
    · have hcard64 : Fintype.card V = 8 * (8 - 1) + 3 + 5 := by
        norm_num at hcard ⊢
        exact hcard
      have hanti := antipodalGraph_degree_eq_excess_add_two_sub_triangleFree
        G hfree (d := 8) (e := 5) (by omega) hreg hcard64 x.1
      have htfcard : (triangleFreeNeighbors G x.1).card =
          (triangleFreeEdgeGraph G).degree x.1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
      rw [htfcard, htwo, hdeg7] at hanti
      omega
  have hsubA : ∀ x : c.supp, x ∈ a.supp →
      r + k ≤ (antipodalGraph G).degree x.1 := by
    intro x hxa
    let X := B.filter fun y ↦ (antipodalGraph G).Adj x.1 y.1
    let Y := A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1
    have hXcard : X.card = r := hcrossA x hxa
    have hxA : x ∈ A := by simpa [A] using hxa
    have hYcard : Y.card = k := hA x hxA
    have hXYdisj : Disjoint X Y := hdisj.symm.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
    let Z : Finset V := (X ∪ Y).image Subtype.val
    have hZcard : Z.card = r + k := by
      rw [show Z.card = (X ∪ Y).card by
        exact Finset.card_image_of_injective _ Subtype.val_injective]
      rw [Finset.card_union_of_disjoint hXYdisj, hXcard, hYcard]
    have hZsub : Z ⊆ (antipodalGraph G).neighborFinset x.1 := by
      intro z hz
      simp only [Z, Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rcases Finset.mem_union.mp hy with hyX | hyY
      · exact ((antipodalGraph G).mem_neighborFinset _ _).mpr
          (Finset.mem_filter.mp hyX).2
      · have hy' := Finset.mem_filter.mp hyY
        exact ((antipodalGraph G).mem_neighborFinset _ _).mpr <|
          (sizeTwo_equalSign_secondOrderDefect_iff_antipodal
            G hfree hreg hcard c hc s hs_in hs_out hAfull x y hy'.2.2).1 hy'.2.1
    rw [← hZcard, ← (antipodalGraph G).card_neighborFinset_eq_degree]
    exact Finset.card_le_card hZsub
  have hsubB : ∀ x : c.supp, x ∈ b.supp →
      r + k ≤ (antipodalGraph G).degree x.1 := by
    intro x hxb
    let X := A.filter fun y ↦ (antipodalGraph G).Adj x.1 y.1
    let Y := B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1
    have hXcard : X.card = r := hcrossB x hxb
    have hxB : x ∈ B := by simpa [B] using hxb
    have hYcard : Y.card = k := hB x hxB
    have hXYdisj : Disjoint X Y := hdisj.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
    let Z : Finset V := (X ∪ Y).image Subtype.val
    have hZcard : Z.card = r + k := by
      rw [show Z.card = (X ∪ Y).card by
        exact Finset.card_image_of_injective _ Subtype.val_injective]
      rw [Finset.card_union_of_disjoint hXYdisj, hXcard, hYcard]
    have hZsub : Z ⊆ (antipodalGraph G).neighborFinset x.1 := by
      intro z hz
      simp only [Z, Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rcases Finset.mem_union.mp hy with hyX | hyY
      · exact ((antipodalGraph G).mem_neighborFinset _ _).mpr
          (Finset.mem_filter.mp hyX).2
      · have hy' := Finset.mem_filter.mp hyY
        exact ((antipodalGraph G).mem_neighborFinset _ _).mpr <|
          (sizeTwo_equalSign_secondOrderDefect_iff_antipodal
            G hfree hreg hcard c hc s hs_in hs_out hAfull x y hy'.2.2).1 hy'.2.1
    rw [← hZcard, ← (antipodalGraph G).card_neighborFinset_eq_degree]
    exact Finset.card_le_card hZsub
  refine ⟨k, r, hk, hr2, hr7, ?_⟩
  intro hcap
  constructor
  · intro x hxa
    apply hfinish x
    simpa [hcap] using hsubA x hxa
  · intro x hxb
    apply hfinish x
    simpa [hcap] using hsubB x hxb

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_capacitySix_allTriangle
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_capacitySix_bothAllTriangle
