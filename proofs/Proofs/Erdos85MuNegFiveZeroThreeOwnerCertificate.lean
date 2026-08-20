import Proofs.Erdos85MuNegFiveZeroThreeOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked owner-CNF certificates for h503

The two compact LRAT traces cover the two relative sign phases of the
`mu = -5`, `(k,r) = (0,3)`, both-all-triangle-free owner model.  Their source
DIMACS formulas have 1,460 variables and 388,440 clauses.  Kissat produced the
DRAT traces; `drat-trim` and `lrat-check` independently verified the resulting
LRAT before compaction.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegFiveZeroThreeS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg5_zerothree_s0.compact.lrat")

def muNegFiveZeroThreeS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg5_zerothree_s1.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveZeroThreeOwner_check_s0 :
    LRAT.check muNegFiveZeroThreeS0Proof
      (muNegFiveZeroThreeSatCnf false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveZeroThreeOwner_check_s1 :
    LRAT.check muNegFiveZeroThreeS1Proof
      (muNegFiveZeroThreeSatCnf true) := by
  native_decide

/-- Both relative sign phases of the h503 owner CNF are unsatisfiable. -/
theorem muNegFiveZeroThreeOwner_unsat (sigma : Bool) :
    (muNegFiveZeroThreeSatCnf sigma).Unsat := by
  cases sigma
  · exact LRAT.check_sound _ _ muNegFiveZeroThreeOwner_check_s0
  · exact LRAT.check_sound _ _ muNegFiveZeroThreeOwner_check_s1

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeOwner_check_s0
#print axioms Erdos85.muNegFiveZeroThreeOwner_check_s1
#print axioms Erdos85.muNegFiveZeroThreeOwner_unsat
