import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighProfileOneAllEvenInventoryTerminal
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked profile-1 all-even reciprocal certificate 8d35c26cc42db606 -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem oneHighProfileOneAllEvenReciprocalInventoryTables_two_lt_length :
    2 < oneHighProfileOneAllEvenReciprocalInventoryTables.length := by
  rw [oneHighProfileOneAllEvenReciprocalInventoryTables_length]
  omega

def oneHighProfileOneAllEvenReciprocalIndex8d35c26cc42db606 :
    Fin oneHighProfileOneAllEvenReciprocalInventoryTables.length :=
  ⟨2, oneHighProfileOneAllEvenReciprocalInventoryTables_two_lt_length⟩

def oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606 :
    OneHighMissTable :=
  oneHighProfileOneAllEvenReciprocalInventoryTables.get
    oneHighProfileOneAllEvenReciprocalIndex8d35c26cc42db606

theorem oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606_mem :
    oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606 ∈
      oneHighProfileOneAllEvenReciprocalInventoryTables := by
  exact List.get_mem _ _

def oneHighProfileOneAllEvenReciprocalProofText8d35c26cc42db606 : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile1-all-even-reciprocal-5/v2-lrat/8d35c26cc42db606.v2.compact.lrat"

def oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606 :
    Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    oneHighProfileOneAllEvenReciprocalProofText8d35c26cc42db606

theorem oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606_size :
    oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606.size = 4942982 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606_check :
    LRAT.check oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606
      (oneHighFamilyV2SatCnf 1
        oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighProfileOneAllEvenReciprocalChecked8d35c26cc42db606 :
    OneHighFamilyV2CheckedUnsat 1
      oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606 :=
  oneHighFamilyV2CheckedUnsat_of_lrat
    oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606_nonzero
    oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606
    oneHighProfileOneAllEvenReciprocalProof8d35c26cc42db606_check

def oneHighProfileOneAllEvenReciprocalEntry8d35c26cc42db606 :
    OneHighFamilyV2CheckedEntry 1 where
  table := oneHighProfileOneAllEvenReciprocalTable8d35c26cc42db606
  checked := oneHighProfileOneAllEvenReciprocalChecked8d35c26cc42db606

end Erdos85
