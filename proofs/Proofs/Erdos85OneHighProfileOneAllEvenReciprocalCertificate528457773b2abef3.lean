import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighProfileOneAllEvenInventoryTerminal
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked profile-1 all-even reciprocal certificate 528457773b2abef3 -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem oneHighProfileOneAllEvenReciprocalInventoryTables_one_lt_length :
    1 < oneHighProfileOneAllEvenReciprocalInventoryTables.length := by
  rw [oneHighProfileOneAllEvenReciprocalInventoryTables_length]
  omega

def oneHighProfileOneAllEvenReciprocalIndex528457773b2abef3 :
    Fin oneHighProfileOneAllEvenReciprocalInventoryTables.length :=
  ⟨1, oneHighProfileOneAllEvenReciprocalInventoryTables_one_lt_length⟩

def oneHighProfileOneAllEvenReciprocalTable528457773b2abef3 :
    OneHighMissTable :=
  oneHighProfileOneAllEvenReciprocalInventoryTables.get
    oneHighProfileOneAllEvenReciprocalIndex528457773b2abef3

theorem oneHighProfileOneAllEvenReciprocalTable528457773b2abef3_mem :
    oneHighProfileOneAllEvenReciprocalTable528457773b2abef3 ∈
      oneHighProfileOneAllEvenReciprocalInventoryTables := by
  exact List.get_mem _ _

def oneHighProfileOneAllEvenReciprocalProofText528457773b2abef3 : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile1-all-even-reciprocal-5/v2-lrat/528457773b2abef3.v2.compact.lrat"

def oneHighProfileOneAllEvenReciprocalProof528457773b2abef3 :
    Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    oneHighProfileOneAllEvenReciprocalProofText528457773b2abef3

theorem oneHighProfileOneAllEvenReciprocalProof528457773b2abef3_size :
    oneHighProfileOneAllEvenReciprocalProof528457773b2abef3.size = 1267732 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighProfileOneAllEvenReciprocalProof528457773b2abef3_check :
    LRAT.check oneHighProfileOneAllEvenReciprocalProof528457773b2abef3
      (oneHighFamilyV2SatCnf 1
        oneHighProfileOneAllEvenReciprocalTable528457773b2abef3) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighProfileOneAllEvenReciprocalProof528457773b2abef3_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTable528457773b2abef3).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTable528457773b2abef3).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighProfileOneAllEvenReciprocalChecked528457773b2abef3 :
    OneHighFamilyV2CheckedUnsat 1
      oneHighProfileOneAllEvenReciprocalTable528457773b2abef3 :=
  oneHighFamilyV2CheckedUnsat_of_lrat
    oneHighProfileOneAllEvenReciprocalProof528457773b2abef3_nonzero
    oneHighProfileOneAllEvenReciprocalProof528457773b2abef3
    oneHighProfileOneAllEvenReciprocalProof528457773b2abef3_check

def oneHighProfileOneAllEvenReciprocalEntry528457773b2abef3 :
    OneHighFamilyV2CheckedEntry 1 where
  table := oneHighProfileOneAllEvenReciprocalTable528457773b2abef3
  checked := oneHighProfileOneAllEvenReciprocalChecked528457773b2abef3

end Erdos85
