import Proofs.Erdos85SizeTwoMuNegOneCycleDefectSectorUniformity
import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourExterior

/-!
# Exact diagonal model in the `mu=-1`, `(k,r)=(1,4)` cell

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Once the signed diagonal classifier supplies the half-turn defect edge, the
quotient-three diagonal row and the uniform cycle sector determine the whole
shore: `{±1,4}` in the triangle-free sector and `{±3,4}` in the all-triangle
sector.  This is the graph-facing composition of the finite row kernels with
the new all-row sector theorem.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- A quotient-three normalized C8 shore containing its half-turn has one of
the two exact diagonal supports required by the `(−1,1,4)` owner models. -/
theorem binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_supports
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
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hfour : ∀ i,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u (i + 4))) :
    (∀ i j, ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
      j - i = 1 ∨ j - i = 4 ∨ j - i = 7) ∨
    (∀ i j, ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 5) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hua (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hrowCard : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (u i) (u j)).card = 3 := by
    intro i
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      K.Adj (u i) (u j)
    let B := componentNeighborFinset K H a (u i)
    have himage : T.image u = B := by
      ext z
      simp only [T, B, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, componentNeighborFinset]
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
    change T.card = 3
    rw [← Finset.card_image_of_injective T huinj, himage]
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a a (hua i)]
    exact haa3
  have hnot26 (i j : ZMod 8)
      (hoff : j - i = 2 ∨ j - i = 6) : ¬ K.Adj (u i) (u j) := by
    have hij : i ≠ j := by
      intro h
      subst j
      exact (by decide : ¬ ((0 : ZMod 8) = 2 ∨ (0 : ZMod 8) = 6))
        (by simpa using hoff)
    obtain ⟨z, hiz, hjz⟩ :=
      (zmodEight_cycle_internalCommon_iff_offset_two_six
        H u huinj hu i j hij).mpr hoff
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree
      (fun h ↦ huinj.ne hij (Subtype.ext h)) hiz hjz
  rcases binarySquare_regular_sizeTwoPart_eight_cycleDefect_allZero_or_allOne
      G hfree hreg hcard c hc a u hurange hu with hzero | hone
  · right
    apply zmodEight_rowsThree_cycleZero_four_sub_iff
      (fun i j ↦ K.Adj (u i) (u j)) hrowCard
    · intro i
      exact K.loopless.irrefl (u i)
    · intro i
      simpa only [show i + 1 = i + 1 by rfl] using (hzero i).2
    · intro i
      exact hnot26 i (i + 2) (Or.inl (by ring))
    · exact hfour
    · intro i
      exact hnot26 i (i + 6) (Or.inr (by ring))
    · intro i
      have hm := (hzero i).1
      rw [show i + 7 = i - 1 by
        exact (by decide : ∀ i : ZMod 8, i + 7 = i - 1) i]
      exact hm
  · left
    apply zmodEight_rowsThree_cycleOne_four_sub_iff
      (fun i j ↦ K.Adj (u i) (u j)) hrowCard
    · intro i
      exact (hone i).2
    · exact hfour
    · intro i
      have hm := (hone i).1
      rw [show i + 7 = i - 1 by
        exact (by decide : ∀ i : ZMod 8, i + 7 = i - 1) i]
      exact hm

/-- Exterior form of the exact shore classification.  The two possible
diagonal defect supports become precisely the two within-shore owner
supports used by the parameter-four CNFs. -/
theorem binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_exterior_supports
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
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hfour : ∀ i,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u (i + 4))) :
    (∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
      j - i = 3 ∨ j - i = 5) ∨
    (∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
      j - i = 1 ∨ j - i = 7) := by
  rcases binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_supports
      G hfree hreg hcard c hc a u huinj hurange hu haa3 hfour with htf | htri
  · left
    exact zmodEight_diagonal_one_four_seven_exterior_iff_three_five
      G hfree c u huinj hu htf
  · right
    exact zmodEight_diagonal_three_four_five_exterior_iff_one_seven
      G hfree c u huinj hu htri

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_supports
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_exterior_supports
