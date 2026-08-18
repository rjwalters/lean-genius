import Proofs.Erdos85OneHighV2Exclusion
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # First checked exact-v2 h=1 orbit certificate -/

namespace Erdos85

open Std.Tactic.BVDecide

def oneHighV2CalibrationTable : OneHighMissTable := fun c j =>
  if c = 0 ∧ j = 5 then 1 else
  if c = 0 ∧ j = 7 then 3 else
  if c = 1 ∧ j = 3 then 1 else
  if c = 1 ∧ j = 4 then 1 else
  if c = 1 ∧ j = 6 then 2 else
  if c = 2 ∧ j = 4 then 2 else
  if c = 2 ∧ j = 6 then 2 else
  if c = 3 ∧ j = 5 then 3 else
  if c = 4 ∧ j = 7 then 1 else 0

def oneHighV2CalibrationProofText : String :=
  include_str "Certificates" / "h1_v2_82cfe9119843719f.compact.lrat"

def oneHighV2CalibrationProof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof oneHighV2CalibrationProofText

theorem oneHighV2CalibrationProof_size :
    oneHighV2CalibrationProof.size = 262488 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighV2Calibration_check :
    LRAT.check oneHighV2CalibrationProof
      (oneHighFamilyV2SatCnf 0 oneHighV2CalibrationTable) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighV2Calibration_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 0
      oneHighV2CalibrationTable).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 0 oneHighV2CalibrationTable).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause
      (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighV2Calibration_checkedUnsat :
    OneHighFamilyV2CheckedUnsat 0 oneHighV2CalibrationTable :=
  oneHighFamilyV2CheckedUnsat_of_lrat oneHighV2Calibration_nonzero
    oneHighV2CalibrationProof oneHighV2Calibration_check

end Erdos85
