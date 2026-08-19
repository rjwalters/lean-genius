import Proofs.Erdos85SizeTwoMuNegThreeSectorSwitchRouting
import Proofs.Erdos85SizeTwoEigenlineEightEightMixedExteriorModel

/-! # The exact diagonal block in the `mu=-3`, `(k,r)=(1,2)` self cell -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A normalized C8 diagonal defect block of row degree five has the unique
support `{±1,±3,4}`: looplessness excludes offset zero and the midpoint
common-neighbor obstruction excludes offsets `±2`. -/
theorem zmodEight_defect_diagonal_rowFive_iff_offset_one_three_four_five_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hrow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j)).card = 5) :
    ∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
          j - i = 5 ∨ j - i = 7 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hnotDistanceTwo (i j : ZMod 8)
      (hoff : j - i = 2 ∨ j - i = 6) : ¬ K.Adj (u i) (u j) := by
    have hij : i ≠ j := by
      intro h
      subst j
      have h02 : (0 : ZMod 8) ≠ 2 := by decide
      have h06 : (0 : ZMod 8) ≠ 6 := by decide
      simpa only [sub_self, h02, h06, or_self] using hoff
    obtain ⟨z, hiz, hjz⟩ :=
      (zmodEight_cycle_internalCommon_iff_offset_two_six
        H u huinj hu i j hij).mpr hoff
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree
      (fun h => huinj.ne hij (Subtype.ext h)) hiz hjz
  let T (i : ZMod 8) := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    K.Adj (u i) (u j)
  let S (i : ZMod 8) := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
      j - i = 5 ∨ j - i = 7
  have hTcard (i : ZMod 8) : (T i).card = 5 := by
    simpa [T, K] using hrow i
  have hScard (i : ZMod 8) : (S i).card = 5 := by
    classical
    fin_cases i <;> decide
  have hsub (i : ZMod 8) : T i ⊆ S i := by
    intro j hj
    have hK : K.Adj (u i) (u j) := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    have hallOffsets : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
        j - i = 6 ∨ j - i = 7 := by
      generalize j - i = d
      revert d
      decide
    rcases hallOffsets with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · have hij : i = j := by exact (sub_eq_zero.mp h0).symm
      exact False.elim (K.ne_of_adj hK (congrArg u hij))
    · exact Or.inl h1
    · exact False.elim (hnotDistanceTwo i j (Or.inl h2) hK)
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
    · exact False.elim (hnotDistanceTwo i j (Or.inr h6) hK)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))
  have heq (i : ZMod 8) : T i = S i := by
    exact Finset.eq_of_subset_of_card_le (hsub i) (by rw [hTcard, hScard])
  intro i j
  have hmemT : j ∈ T i ↔ K.Adj (u i) (u j) := by simp [T]
  have hmemS : j ∈ S i ↔
      j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7 := by simp [S]
  rw [← hmemT, heq, hmemS]

/-- Quotient-native form of the row-five classification.  This is the form
needed by the `(k,r) = (1,2)` cell: its diagonal quotient entry is
`7 - r = 5`. -/
theorem binarySquare_regular_sizeTwoPart_eight_diagonalFive_defectAdj_iff_offset_one_three_four_five_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haa5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 5) :
    ∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
          j - i = 5 ∨ j - i = 7 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hua (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hrow : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (u i) (u j)).card = 5 := by
    intro i
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      K.Adj (u i) (u j)
    let B := componentNeighborFinset K H a (u i)
    have himage : T.image u = B := by
      ext z
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B, componentNeighborFinset]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(K.mem_neighborFinset _ _).mpr hj,
          (ConnectedComponent.mem_supp_iff a (u j)).mp (hua j)⟩
      · rintro ⟨hzK, hza⟩
        have hzA : z ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a z).mpr hza
        rw [← hurange] at hzA
        obtain ⟨j, rfl⟩ := hzA
        exact ⟨j, (K.mem_neighborFinset _ _).mp hzK, rfl⟩
    change T.card = 5
    rw [← Finset.card_image_of_injective T huinj, himage]
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a a (hua i)]
    exact haa5
  exact zmodEight_defect_diagonal_rowFive_iff_offset_one_three_four_five_seven
    G hfree c u huinj hu hrow

/-- A diagonal-five C8 shore has no exterior pair internally: every
nontrivial offset is either a defect edge (`±1,±3,4`) or has an internal
common neighbor (`±2`). -/
theorem binarySquare_regular_sizeTwoPart_eight_diagonalFive_no_internal_exteriorPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haa5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 5) :
    ∀ i j, ¬ (exteriorPairGraph G c.supp).Adj (u i) (u j) := by
  classical
  let H := G.induce c.supp
  have hD :=
    binarySquare_regular_sizeTwoPart_eight_diagonalFive_defectAdj_iff_offset_one_three_four_five_seven
      G hfree hreg hcard c hc a u huinj hurange hu haa5
  intro i j hext
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    G hfree c] at hext
  have hall : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
      j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
      j - i = 6 ∨ j - i = 7 := by
    generalize j - i = d
    revert d
    decide
  rcases hall with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hij : i = j := (sub_eq_zero.mp h0).symm
    exact hext.1 (congrArg u hij)
  · exact hext.2.1 ((hD i j).mpr (Or.inl h1))
  · apply hext.2.2
    exact (zmodEight_cycle_internalCommon_iff_offset_two_six
      H u huinj hu i j (by
        intro hij
        subst j
        simp only [sub_self] at h2
        exact (by decide : (0 : ZMod 8) ≠ 2) h2)).mpr (Or.inl h2)
  · exact hext.2.1 ((hD i j).mpr (Or.inr (Or.inl h3)))
  · exact hext.2.1 ((hD i j).mpr (Or.inr (Or.inr (Or.inl h4))))
  · exact hext.2.1 ((hD i j).mpr
      (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · apply hext.2.2
    exact (zmodEight_cycle_internalCommon_iff_offset_two_six
      H u huinj hu i j (by
        intro hij
        subst j
        simp only [sub_self] at h6
        exact (by decide : (0 : ZMod 8) ≠ 6) h6)).mpr (Or.inr h6)
  · exact hext.2.1 ((hD i j).mpr
      (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

end


end Erdos85

#print axioms Erdos85.zmodEight_defect_diagonal_rowFive_iff_offset_one_three_four_five_seven
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_diagonalFive_defectAdj_iff_offset_one_three_four_five_seven
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_diagonalFive_no_internal_exteriorPair
