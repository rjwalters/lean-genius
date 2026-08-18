import Proofs.Erdos85MuThreeFixedKSlotManifest

/-!
# Internal-H equality audit for the fixed-K manifest

The certificate records store their internal two-factor as a Boolean table,
while the exhaustive dispatcher stores it as the sector's row function.  The
following theorem is the exact `hinternal` premise of the mixed-grid native
adapter.
-/

namespace Erdos85

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A fixed target's sector H relation is exactly the internal relation in
the corresponding native grid record. -/
theorem Mu3KCandidateSlot.internal_iff_fixed_grid
    (slot : Mu3KCandidateSlot) (x y : Fin 8) :
    y.val ∈ slot.sector.HRows x.val ↔
      (mu3FixedKGrid slot.certificateGridIndex).internal
        x.val y.val = true := by
  cases slot <;> rename_i j
  all_goals first | exact Fin.elim0 j | fin_cases j <;> decide +revert

end Erdos85

#print axioms Erdos85.Mu3KCandidateSlot.internal_iff_fixed_grid
