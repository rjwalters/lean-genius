import Proofs.Erdos85OrderFortyNineThreeHighDistTwoNormalization

/-! # Distance-two three-high scout terminal -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The exact three normalized high neighborhoods determine the complete
small-high mask labeling.  The final partition field is then the general
order-49 low/high common-neighbor theorem. -/
theorem orderFortyNineThreeHighDistTwo_smallHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v1 v2 v3 : Fin 49}
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3})
    (E : Equiv.Perm (Fin 49))
    (hEv1 : E v1 = 0) (hEv2 : E v2 = 1) (hEv3 : E v3 = 2)
    (hN0 : (orderFortyNineRelabeledGraph G E).neighborFinset 0 =
      Finset.univ.image orderFortyNineDistTwoFirstTarget)
    (hN1 : (orderFortyNineRelabeledGraph G E).neighborFinset 1 =
      Finset.univ.image orderFortyNineDistTwoSecondTarget)
    (hN2 : (orderFortyNineRelabeledGraph G E).neighborFinset 2 =
      Finset.univ.image orderFortyNineDistTwoThirdTarget) :
    SmallHighAlignedLabeling 3 G E orderFortyNineThreeHighDistTwoMasks := by
  let H := orderFortyNineRelabeledGraph G E
  letI : DecidableRel (antipodalGraph H).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph H).Adj := Classical.decRel _
  have hdegree : ∀ i : Fin 49, H.degree i =
      if i.val < 3 then 8 else 7 := by
    intro i
    by_cases hi : i.val < 3
    · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · rw [if_pos (by omega), ← H.card_neighborFinset_eq_degree, hN0]
        decide
      · rw [if_pos (by omega), ← H.card_neighborFinset_eq_degree, hN1]
        decide
      · rw [if_pos (by omega), ← H.card_neighborFinset_eq_degree, hN2]
        decide
    · rw [if_neg hi, orderFortyNineRelabeledGraph_degree]
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin (Fintype.card_fin 49) (E.symm i) with h7 | h8
      · exact h7
      · exfalso
        have hm : E.symm i = v1 ∨ E.symm i = v2 ∨ E.symm i = v3 := by
          have : E.symm i ∈ orderFortyNineHighVertices G :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h8⟩
          rw [hHigh] at this
          simpa using this
        rcases hm with hm | hm | hm
        · apply hi
          have : i = 0 := by
            have h := congrArg E hm
            simpa [hEv1] using h
          simp [this]
        · apply hi
          have : i = 1 := by
            have h := congrArg E hm
            simpa [hEv2] using h
          simp [this]
        · apply hi
          have : i = 2 := by
            have h := congrArg E hm
            simpa [hEv3] using h
          simp [this]
  have hsupport : ∀ i : Fin 49, ∀ w : Fin 9, w.val < 3 →
      decide (H.Adj i ⟨w.val, by omega⟩) =
        (orderFortyNineSupportMask orderFortyNineThreeHighDistTwoMasks i).getLsbD w.val := by
    intro i w hw
    have hAdj0 : H.Adj i 0 ↔
        i ∈ Finset.univ.image orderFortyNineDistTwoFirstTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN0]
    have hAdj1 : H.Adj i 1 ↔
        i ∈ Finset.univ.image orderFortyNineDistTwoSecondTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN1]
    have hAdj2 : H.Adj i 2 ↔
        i ∈ Finset.univ.image orderFortyNineDistTwoThirdTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN2]
    have hw' : w = 0 ∨ w = 1 ∨ w = 2 := by omega
    rcases hw' with rfl | rfl | rfl
    · rw [Bool.eq_iff_iff, decide_eq_true_eq]
      change H.Adj i 0 ↔ _
      rw [hAdj0]
      fin_cases i <;> decide
    · rw [Bool.eq_iff_iff, decide_eq_true_eq]
      change H.Adj i 1 ↔ _
      rw [hAdj1]
      fin_cases i <;> decide
    · rw [Bool.eq_iff_iff, decide_eq_true_eq]
      change H.Adj i 2 ↔ _
      rw [hAdj2]
      fin_cases i <;> decide
  refine ⟨orderFortyNineThreeHighDistTwoMasks_size, hdegree, hsupport, ?_⟩
  intro i hi w hw
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have hfiber : orderFortyNineSupportFiber
      orderFortyNineThreeHighDistTwoMasks w = H.neighborFinset wi := by
    ext k
    simp only [orderFortyNineSupportFiber, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hs := hsupport k w hw
    rw [← hs]
    simp [wi, H.adj_comm, SimpleGraph.mem_neighborFinset]
  rw [hfiber]
  have hi3 : ¬ i.val < 3 := by omega
  have hwi3 : wi.val < 3 := by simpa [wi] using hw
  exact orderFortyNine_low_high_card_common_eq_one H
    (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
    (fun x => by rw [hdegree]; split <;> omega)
    (Fintype.card_fin 49)
    (by simpa [hi3] using hdegree i)
    (by simpa [hwi3] using hdegree wi)

/-- Full graph-to-LRAT contradiction for the distance-two three-high case.
Only the checked LRAT array remains external to this structural theorem. -/
theorem false_of_orderFortyNine_threeHighDistTwo_lrat
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v1 v2 v3 sStar : Fin 49}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8) (hsLow : G.degree sStar = 7)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hs1 : G.Adj sStar v1) (hs2 : G.Adj sStar v2)
    (hs3 : G.Adj sStar v3)
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3})
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      orderFortyNineGeneratedThreeHighDistTwoScoutCnf) : False := by
  obtain ⟨E, hEv1, hEv2, hEv3, hN0, hN1, hN2,
      hmatch0, hmatch1, hmatch2, hroot⟩ :=
    exists_orderFortyNine_threeHighDistTwo_geometryLabeling
      G hfree hmin (Fintype.card_fin 49) hv1 hv2 hv3 hsLow
      h12 h13 h23 hs1 hs2 hs3 hHigh
  have haligned : ThreeHighDistTwoScoutAlignedLabeling G E :=
    ⟨orderFortyNineThreeHighDistTwo_smallHighAlignedLabeling
      G hfree hmin hHigh E hEv1 hEv2 hEv3 hN0 hN1 hN2,
      hmatch0, hmatch1, hmatch2, hroot⟩
  exact false_of_threeHighDistTwoScoutAlignedLabeling_lrat
    G hfree E haligned proof hcheck

end

end Erdos85
