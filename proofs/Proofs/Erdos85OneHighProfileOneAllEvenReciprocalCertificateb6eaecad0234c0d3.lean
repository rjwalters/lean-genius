import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighProfileOneAllEvenInventoryTerminal
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked profile-1 all-even reciprocal certificate b6eaecad0234c0d3 -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem oneHighProfileOneAllEvenReciprocalInventoryTables_three_lt_length :
    3 < oneHighProfileOneAllEvenReciprocalInventoryTables.length := by
  rw [oneHighProfileOneAllEvenReciprocalInventoryTables_length]
  omega

def oneHighProfileOneAllEvenReciprocalIndexb6eaecad0234c0d3 :
    Fin oneHighProfileOneAllEvenReciprocalInventoryTables.length :=
  ⟨3, oneHighProfileOneAllEvenReciprocalInventoryTables_three_lt_length⟩

def oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3 :
    OneHighMissTable :=
  oneHighProfileOneAllEvenReciprocalInventoryTables.get
    oneHighProfileOneAllEvenReciprocalIndexb6eaecad0234c0d3

theorem oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3_mem :
    oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3 ∈
      oneHighProfileOneAllEvenReciprocalInventoryTables := by
  exact List.get_mem _ _

def oneHighProfileOneAllEvenReciprocalProofTextb6eaecad0234c0d3 : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile1-all-even-reciprocal-5/v2-lrat/b6eaecad0234c0d3.v2.compact.lrat"

def oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3 :
    Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    oneHighProfileOneAllEvenReciprocalProofTextb6eaecad0234c0d3

theorem oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3_size :
    oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3.size = 3091546 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3_check :
    LRAT.check oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3
      (oneHighFamilyV2SatCnf 1
        oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighProfileOneAllEvenReciprocalCheckedb6eaecad0234c0d3 :
    OneHighFamilyV2CheckedUnsat 1
      oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3 :=
  oneHighFamilyV2CheckedUnsat_of_lrat
    oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3_nonzero
    oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3
    oneHighProfileOneAllEvenReciprocalProofb6eaecad0234c0d3_check

def oneHighProfileOneAllEvenReciprocalEntryb6eaecad0234c0d3 :
    OneHighFamilyV2CheckedEntry 1 where
  table := oneHighProfileOneAllEvenReciprocalTableb6eaecad0234c0d3
  checked := oneHighProfileOneAllEvenReciprocalCheckedb6eaecad0234c0d3

end Erdos85
