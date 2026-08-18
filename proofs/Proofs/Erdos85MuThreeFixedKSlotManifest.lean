import Proofs.Erdos85MuThreeFixedKNativeData
import Proofs.Erdos85MuThreeKSymmetryCandidateSlots

/-!
# Equality audit for the fixed-K certificate manifest

The nineteen generated certificates use explicit occupied-cell lists.  This
module checks that those lists are exactly the complements of the K tables
selected by the exhaustive dispatcher, in the dispatcher's declared order.
-/

namespace Erdos85

/-- The row-table representation of the 48 occupied cells: a cell is present
exactly when it is not one of the sixteen K holes. -/
def mu3KCandidateSlotCells (slot : Mu3KCandidateSlot) : List Nat :=
  (List.range 64).filter fun cell =>
    decide (cell % 8 ∉ slot.rows.getD (cell / 8) ∅)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Every fixed dispatcher target has exactly the occupied-cell list embedded
in its native certificate record. -/
theorem Mu3KCandidateSlot.fixed_grid_cells
    (slot : Mu3KCandidateSlot) (i : Fin 19)
    (h : slot.certificateTarget = .fixed i) :
    (mu3FixedKGrid i).cells = mu3KCandidateSlotCells slot := by
  cases slot with
  | c16AllTf j => simp [Mu3KCandidateSlot.certificateTarget] at h
  | c16AllTriangle j =>
      fin_cases j <;>
        simp [Mu3KCandidateSlot.certificateTarget] at h <;>
        subst i <;> native_decide
  | c88AllTf j => simp [Mu3KCandidateSlot.certificateTarget] at h
  | c88AllTriangle j =>
      fin_cases j <;>
        simp [Mu3KCandidateSlot.certificateTarget] at h <;>
        subst i <;> native_decide
  | c88FirstTf j =>
      fin_cases j
      simp [Mu3KCandidateSlot.certificateTarget] at h
      subst i
      native_decide
  | c88SecondTf j =>
      fin_cases j
      simp [Mu3KCandidateSlot.certificateTarget] at h
      subst i
      native_decide
  | c106AllTf j => simp [Mu3KCandidateSlot.certificateTarget] at h
  | c106AllTriangle j => exact Fin.elim0 j
  | c106TenTf j => exact Fin.elim0 j
  | c106SixTf j =>
      fin_cases j
      simp [Mu3KCandidateSlot.certificateTarget] at h
      subst i
      native_decide

end Erdos85

#print axioms Erdos85.Mu3KCandidateSlot.fixed_grid_cells
