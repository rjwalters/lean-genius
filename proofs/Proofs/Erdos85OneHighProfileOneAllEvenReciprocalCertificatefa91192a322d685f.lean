import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighProfileOneAllEvenInventoryTerminal
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked profile-1 all-even reciprocal certificate fa91192a322d685f -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem oneHighProfileOneAllEvenReciprocalInventoryTables_four_lt_length :
    4 < oneHighProfileOneAllEvenReciprocalInventoryTables.length := by
  rw [oneHighProfileOneAllEvenReciprocalInventoryTables_length]
  omega

def oneHighProfileOneAllEvenReciprocalIndexfa91192a322d685f :
    Fin oneHighProfileOneAllEvenReciprocalInventoryTables.length :=
  ⟨4, oneHighProfileOneAllEvenReciprocalInventoryTables_four_lt_length⟩

def oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f :
    OneHighMissTable :=
  oneHighProfileOneAllEvenReciprocalInventoryTables.get
    oneHighProfileOneAllEvenReciprocalIndexfa91192a322d685f

theorem oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f_mem :
    oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f ∈
      oneHighProfileOneAllEvenReciprocalInventoryTables := by
  exact List.get_mem _ _

def oneHighProfileOneAllEvenReciprocalProofTextfa91192a322d685f : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile1-all-even-reciprocal-5/v2-lrat/fa91192a322d685f.v2.compact.lrat"

def oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f :
    Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    oneHighProfileOneAllEvenReciprocalProofTextfa91192a322d685f

theorem oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f_size :
    oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f.size = 4177005 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f_check :
    LRAT.check oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f
      (oneHighFamilyV2SatCnf 1
        oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighProfileOneAllEvenReciprocalCheckedfa91192a322d685f :
    OneHighFamilyV2CheckedUnsat 1
      oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f :=
  oneHighFamilyV2CheckedUnsat_of_lrat
    oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f_nonzero
    oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f
    oneHighProfileOneAllEvenReciprocalProoffa91192a322d685f_check

def oneHighProfileOneAllEvenReciprocalEntryfa91192a322d685f :
    OneHighFamilyV2CheckedEntry 1 where
  table := oneHighProfileOneAllEvenReciprocalTablefa91192a322d685f
  checked := oneHighProfileOneAllEvenReciprocalCheckedfa91192a322d685f

end Erdos85
