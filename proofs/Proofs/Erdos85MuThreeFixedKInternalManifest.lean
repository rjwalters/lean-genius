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
    (slot : Mu3KCandidateSlot) (i : Fin 19)
    (h : slot.certificateTarget = .fixed i) (x y : Fin 8) :
    y.val ∈ slot.sector.HRows x.val ↔
      (mu3FixedKGrid i).internal x.val y.val = true := by
  cases slot with
  | c16AllTf j => simp [Mu3KCandidateSlot.certificateTarget] at h
  | c16AllTriangle j =>
      fin_cases j <;>
        simp [Mu3KCandidateSlot.certificateTarget] at h <;>
        subst i <;> fin_cases x <;> fin_cases y <;> decide
  | c88AllTf j => simp [Mu3KCandidateSlot.certificateTarget] at h
  | c88AllTriangle j =>
      fin_cases j <;>
        simp [Mu3KCandidateSlot.certificateTarget] at h <;>
        subst i <;> fin_cases x <;> fin_cases y <;> decide
  | c88FirstTf j =>
      fin_cases j
      simp [Mu3KCandidateSlot.certificateTarget] at h
      subst i
      fin_cases x <;> fin_cases y <;> decide
  | c88SecondTf j =>
      fin_cases j
      simp [Mu3KCandidateSlot.certificateTarget] at h
      subst i
      fin_cases x <;> fin_cases y <;> decide
  | c106AllTf j => simp [Mu3KCandidateSlot.certificateTarget] at h
  | c106AllTriangle j => exact Fin.elim0 j
  | c106TenTf j => exact Fin.elim0 j
  | c106SixTf j =>
      fin_cases j
      simp [Mu3KCandidateSlot.certificateTarget] at h
      subst i
      fin_cases x <;> fin_cases y <;> decide

end Erdos85

#print axioms Erdos85.Mu3KCandidateSlot.internal_iff_fixed_grid
