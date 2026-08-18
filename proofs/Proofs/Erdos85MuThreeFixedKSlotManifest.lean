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
/-- Every dispatcher slot has exactly the occupied-cell list embedded in its
uniform native certificate record. -/
theorem Mu3KCandidateSlot.fixed_grid_cells (slot : Mu3KCandidateSlot) :
    (mu3FixedKGrid slot.certificateGridIndex).cells =
      mu3KCandidateSlotCells slot := by
  cases slot <;> rename_i j
  all_goals first | exact Fin.elim0 j | fin_cases j <;> native_decide

/-- Assembly-facing form of the manifest audit: the complement of the slot's
Boolean K relation is precisely the occupied-cell predicate expected by the
fixed-K mixed-grid adapter. -/
theorem Mu3KCandidateSlot.not_candidate_iff_fixed_grid_mem
    (slot : Mu3KCandidateSlot) (x y : Fin 8) :
    ¬ mu3KRowsCandidate slot.rows x y = true ↔
      x.val * 8 + y.val ∈
        (mu3FixedKGrid slot.certificateGridIndex).cells := by
  rw [slot.fixed_grid_cells]
  simp only [mu3KCandidateSlotCells, List.mem_filter, List.mem_range,
    decide_eq_true_eq, mu3KRowsCandidate_eq_true_iff]
  have hcode : x.val * 8 + y.val < 64 := by omega
  have hdiv : (x.val * 8 + y.val) / 8 = x.val := by omega
  have hmod : (x.val * 8 + y.val) % 8 = y.val := by omega
  simp [hcode, hdiv, hmod]

end Erdos85

#print axioms Erdos85.Mu3KCandidateSlot.fixed_grid_cells
#print axioms Erdos85.Mu3KCandidateSlot.not_candidate_iff_fixed_grid_mem
