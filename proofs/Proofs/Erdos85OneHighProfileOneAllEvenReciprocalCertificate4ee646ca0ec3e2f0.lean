import Proofs.Erdos85OneHighV2CertificateAggregation
import Proofs.Erdos85OneHighProfileOneAllEvenInventoryTerminal
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-! # Checked profile-1 all-even reciprocal certificate 4ee646ca0ec3e2f0

The payload was generated from the Lean-exact profile-1 CNF, independently
checked by `drat-trim` and `lrat-check`, compact-renumbered, and accepted by
the same Lean LRAT runtime used below.
-/

namespace Erdos85

open Std.Tactic.BVDecide

theorem oneHighProfileOneAllEvenReciprocalInventoryTables_nonempty :
    oneHighProfileOneAllEvenReciprocalInventoryTables ≠ [] := by
  intro h
  have hlen := oneHighProfileOneAllEvenReciprocalInventoryTables_length
  rw [h] at hlen
  simp at hlen

def oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0 :
    OneHighMissTable :=
  oneHighProfileOneAllEvenReciprocalInventoryTables.head
    oneHighProfileOneAllEvenReciprocalInventoryTables_nonempty

theorem oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0_mem :
    oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0 ∈
      oneHighProfileOneAllEvenReciprocalInventoryTables := by
  exact List.head_mem
    oneHighProfileOneAllEvenReciprocalInventoryTables_nonempty

def oneHighProfileOneAllEvenReciprocalProofText4ee646ca0ec3e2f0 : String :=
  include_str "/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h1-profile1-all-even-reciprocal-5/v2-lrat/4ee646ca0ec3e2f0.v2.compact.lrat"

def oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0 :
    Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    oneHighProfileOneAllEvenReciprocalProofText4ee646ca0ec3e2f0

theorem oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0_size :
    oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0.size = 3431280 := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0_check :
    LRAT.check oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0
      (oneHighFamilyV2SatCnf 1
        oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0) := by
  native_decide

set_option maxHeartbeats 0 in
theorem oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0_nonzero :
    ∀ clause ∈ (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0).clauses,
      DimacsClauseNonzero clause := by
  have h : (oneHighFamilyV2Clauses 1
      oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp h) clause (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

theorem oneHighProfileOneAllEvenReciprocalChecked4ee646ca0ec3e2f0 :
    OneHighFamilyV2CheckedUnsat 1
      oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0 :=
  oneHighFamilyV2CheckedUnsat_of_lrat
    oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0_nonzero
    oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0
    oneHighProfileOneAllEvenReciprocalProof4ee646ca0ec3e2f0_check

def oneHighProfileOneAllEvenReciprocalEntry4ee646ca0ec3e2f0 :
    OneHighFamilyV2CheckedEntry 1 where
  table := oneHighProfileOneAllEvenReciprocalTable4ee646ca0ec3e2f0
  checked := oneHighProfileOneAllEvenReciprocalChecked4ee646ca0ec3e2f0

end Erdos85
