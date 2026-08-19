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

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_capacitySix_allTriangle
