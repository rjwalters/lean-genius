import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked profile-2 reciprocal inventory certificate 01c2be116496a476 -/

namespace Erdos85

open Std.Tactic.BVDecide

def oneHighProfileTwoReciprocalTable01c2be116496a476 : OneHighMissTable :=
  (oneHighInventoryTables (2 : Fin 5)).get ⟨30, by native_decide⟩

def oneHighProfileTwoReciprocalProofText01c2be116496a476 : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/v2-lrat/01c2be116496a476.v2.compact.lrat"

def oneHighProfileTwoReciprocalProof01c2be116496a476 : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof oneHighProfileTwoReciprocalProofText01c2be116496a476

theorem oneHighProfileTwoReciprocalProof01c2be116496a476_size :
    oneHighProfileTwoReciprocalProof01c2be116496a476.size = 537792 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighProfileTwoReciprocalProof01c2be116496a476_check :
    LRAT.check oneHighProfileTwoReciprocalProof01c2be116496a476
      (oneHighFamilyV2SatCnf 2 oneHighProfileTwoReciprocalTable01c2be116496a476) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighProfileTwoReciprocalProof01c2be116496a476_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 2
      oneHighProfileTwoReciprocalTable01c2be116496a476).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 2
      oneHighProfileTwoReciprocalTable01c2be116496a476).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighProfileTwoReciprocalChecked01c2be116496a476 :
    OneHighFamilyV2CheckedUnsat 2
      oneHighProfileTwoReciprocalTable01c2be116496a476 :=
  oneHighFamilyV2CheckedUnsat_of_lrat
    oneHighProfileTwoReciprocalProof01c2be116496a476_nonzero
    oneHighProfileTwoReciprocalProof01c2be116496a476
    oneHighProfileTwoReciprocalProof01c2be116496a476_check

def oneHighProfileTwoReciprocalEntry01c2be116496a476 :
    OneHighFamilyV2CheckedEntry 2 where
  table := oneHighProfileTwoReciprocalTable01c2be116496a476
  checked := oneHighProfileTwoReciprocalChecked01c2be116496a476

end Erdos85
