import Proofs.Erdos85SizeTwoEigenlineEightEightHighCrossAntipodal
import Proofs.Erdos85SizeTwoEigenlineEightEightBothTriangleExteriorModel

/-!
# Exterior-pair coordinates for the high eight-plus-eight cross block

These lemmas deliberately stop short of choosing a cyclic phase for the
cross block.  The checked high owner CNF carries those cross bits itself, so
the graph adapter only needs the exact within-shore relation and the fact
that cross exterior pairs are the complement of cross defect adjacency.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- If the diagonal defect block of a labeled C8 is the half-turn matching,
then its exterior-pair block consists exactly of offsets `±1, ±3`. -/
theorem sizeTwo_eight_halfTurnDefect_exteriorPair_iff_odd_nonzero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (hD : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (w i) (w j) ↔
        j - i = 4) :
    ∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (w i) (w j) ↔
      j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
  let H := G.induce c.supp
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have hcommon (hij : i ≠ j) :
      (∃ z, H.Adj (w i) z ∧ H.Adj (w j) z) ↔
        j - i = 2 ∨ j - i = 6 :=
    zmodEight_cycle_internalCommon_iff_offset_two_six H w hwinj hw i j hij
  constructor
  · rintro ⟨hij, hnotD, hnoCommon⟩
    have hij' : i ≠ j := fun h => hij (congrArg w h)
    have hnot4 : j - i ≠ 4 := by
      intro h4
      exact hnotD ((hD i j).mpr h4)
    have hnotCommon : ¬ (j - i = 2 ∨ j - i = 6) := by
      intro hoff
      apply hnoCommon
      simpa [H] using (hcommon hij').mpr hoff
    have hall : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
        j - i = 6 ∨ j - i = 7 := by
      generalize j - i = d
      revert d
      decide
    have hnot0 : j - i ≠ 0 := by
      intro h0
      apply hij'
      exact (sub_eq_zero.mp h0).symm
    tauto
  · intro hoff
    have hij' : i ≠ j := by
      intro h
      subst j
      have hzero : ¬ ((0 : ZMod 8) = 1 ∨ (0 : ZMod 8) = 3 ∨
          (0 : ZMod 8) = 5 ∨ (0 : ZMod 8) = 7) := by decide
      exact hzero (by simpa using hoff)
    refine ⟨hwinj.ne hij', ?_, ?_⟩
    · intro hDij
      have h4 := (hD i j).mp (by simpa using hDij)
      rcases hoff with h1 | h3 | h5 | h7
      · rw [h1] at h4; revert h4; decide
      · rw [h3] at h4; revert h4; decide
      · rw [h5] at h4; revert h4; decide
      · rw [h7] at h4; revert h4; decide
    · intro hex
      have hc := (hcommon hij').mp (by simpa [H] using hex)
      rcases hoff with h1 | h3 | h5 | h7
      · rw [h1] at hc; revert hc; decide
      · rw [h3] at hc; revert hc; decide
      · rw [h5] at hc; revert hc; decide
      · rw [h7] at hc; revert hc; decide

/-- Between two distinct ambient-cycle components there is no internal
common neighbor.  Hence a cross pair is owned outside exactly when it is a
cross defect nonedge. -/
theorem sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
      ¬ ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j) := by
  let H := G.induce c.supp
  have hua : ∀ i, H.connectedComponentMk (u i) = a := by
    intro i
    exact (ConnectedComponent.mem_supp_iff a (u i)).mp (by
      rw [← hurange]
      exact ⟨i, rfl⟩)
  have hvb : ∀ j, H.connectedComponentMk (v j) = b := by
    intro j
    exact (ConnectedComponent.mem_supp_iff b (v j)).mp (by
      rw [← hvrange]
      exact ⟨j, rfl⟩)
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have hne : u i ≠ v j := by
    intro huv
    apply hab
    rw [← hua i, ← hvb j, huv]
  have hnoCommon := distinct_components_no_internalCommon
    H a b hab u v hua hvb i j
  constructor
  · exact fun h => h.2.1
  · intro hnotD
    exact ⟨hne, hnotD, by simpa [H] using hnoCommon⟩

end

end Erdos85

#print axioms Erdos85.sizeTwo_eight_halfTurnDefect_exteriorPair_iff_odd_nonzero
#print axioms Erdos85.sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
