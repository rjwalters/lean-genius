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

end


end Erdos85

#print axioms Erdos85.zmodEight_defect_diagonal_rowFive_iff_offset_one_three_four_five_seven
