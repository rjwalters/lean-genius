import Proofs.Erdos85SizeTwoEigenlineEightEightLowExteriorModel

/-! # Correct within-shore geometry of the h305 endpoint -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The cycle-entry-zero h305 shore has exterior offsets `±1` together
with the fixed antipodal offset `4`. -/
def MuNegThreeZeroFiveTriangleShoreMode
    {X : Type*} (R : SimpleGraph X) (u : ZMod 8 → X) : Prop :=
  ∀ i j, R.Adj (u i) (u j) ↔
    j - i = 1 ∨ j - i = 4 ∨ j - i = 7

/-- The cycle-entry-one h305 shore has exterior offsets `±3` together
with the same fixed antipodal offset `4`. -/
def MuNegThreeZeroFiveTfShoreMode
    {X : Type*} (R : SimpleGraph X) (u : ZMod 8 → X) : Prop :=
  ∀ i j, R.Adj (u i) (u j) ↔
    j - i = 3 ∨ j - i = 4 ∨ j - i = 5

/-- Converting an exact within-shore defect mode into exterior-pair
geometry necessarily retains offset `4`.  This is the correction to the
two-offset h114 shore modes, which cannot be reused verbatim at h305. -/
theorem h305_correct_exterior_shore_modes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    ((∀ i j, K.Adj (u i) (u j) ↔ j - i = 3 ∨ j - i = 5) →
      MuNegThreeZeroFiveTriangleShoreMode
        (exteriorPairGraph G c.supp) u) ∧
    ((∀ i j, K.Adj (u i) (u j) ↔ j - i = 1 ∨ j - i = 7) →
      MuNegThreeZeroFiveTfShoreMode
        (exteriorPairGraph G c.supp) u) := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  have common (i j : ZMod 8) (hij : i ≠ j) :
      ((∃ z : c.supp, G.Adj (u i).1 z.1 ∧ G.Adj (u j).1 z.1) ↔
        j - i = 2 ∨ j - i = 6) := by
    simpa using zmodEight_cycle_internalCommon_iff_offset_two_six
      (G.induce c.supp) u huinj hu i j hij
  constructor
  · intro hD i j
    by_cases hij : i = j
    · subst j; simp [MuNegThreeZeroFiveTriangleShoreMode] <;> decide
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
      G hfree c]
    rw [show (secondOrderDefectGraph G).Adj (u i).1 (u j).1 ↔
      j - i = 3 ∨ j - i = 5 by simpa [K] using hD i j, common i j hij]
    have hne : u i ≠ u j := fun h ↦ hij (huinj h)
    rw [and_iff_right hne]
    have hd0 : j - i ≠ 0 := fun h ↦ hij (sub_eq_zero.mp h).symm
    change (¬(j - i = 3 ∨ j - i = 5) ∧
      ¬(j - i = 2 ∨ j - i = 6)) ↔ _
    generalize j - i = d at hd0 ⊢
    revert d
    decide
  · intro hD i j
    by_cases hij : i = j
    · subst j; simp [MuNegThreeZeroFiveTfShoreMode] <;> decide
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
      G hfree c]
    rw [show (secondOrderDefectGraph G).Adj (u i).1 (u j).1 ↔
      j - i = 1 ∨ j - i = 7 by simpa [K] using hD i j, common i j hij]
    have hne : u i ≠ u j := fun h ↦ hij (huinj h)
    rw [and_iff_right hne]
    have hd0 : j - i ≠ 0 := fun h ↦ hij (sub_eq_zero.mp h).symm
    change (¬(j - i = 1 ∨ j - i = 7) ∧
      ¬(j - i = 2 ∨ j - i = 6)) ↔ _
    generalize j - i = d at hd0 ⊢
    revert d
    decide

end

end Erdos85

#print axioms Erdos85.h305_correct_exterior_shore_modes
