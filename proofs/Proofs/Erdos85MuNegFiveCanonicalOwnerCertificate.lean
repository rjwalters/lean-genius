import Proofs.Erdos85MuNegFiveCanonicalOwnerCnf
import Proofs.Erdos85OrderFortyNineLratCertificateBase

/-!
# Checked owner-CNF certificates for h504 and h512

The four compact LRAT traces cover both relative sign phases of the two
remaining canonical `mu = -5` owner models.  Kissat produced DRAT traces and
`drat-trim` verified them while emitting LRAT; the compact traces are replayed
again below by Lean's LRAT checker.
-/

namespace Erdos85

open Std Sat Std.Tactic.BVDecide

def muNegFiveZeroFourS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg5_zerofour_s0.compact.lrat")

def muNegFiveZeroFourS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg5_zerofour_s1.compact.lrat")

def muNegFiveOneTwoS0Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg5_onetwo_s0.compact.lrat")

def muNegFiveOneTwoS1Proof : Array LRAT.IntAction :=
  parseOrderFortyNineLratProof
    (include_str "Certificates" / "muneg5_onetwo_s1.compact.lrat")

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveZeroFourOwner_check_s0 :
    LRAT.check muNegFiveZeroFourS0Proof
      (muNegFiveZeroFourOwnerSatCnf false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveZeroFourOwner_check_s1 :
    LRAT.check muNegFiveZeroFourS1Proof
      (muNegFiveZeroFourOwnerSatCnf true) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveOneTwoOwner_check_s0 :
    LRAT.check muNegFiveOneTwoS0Proof
      (muNegFiveOneTwoOwnerSatCnf false) := by
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem muNegFiveOneTwoOwner_check_s1 :
    LRAT.check muNegFiveOneTwoS1Proof
      (muNegFiveOneTwoOwnerSatCnf true) := by
  native_decide

theorem muNegFiveZeroFourOwner_unsat (sigma : Bool) :
    (muNegFiveZeroFourOwnerSatCnf sigma).Unsat := by
  cases sigma
  · exact LRAT.check_sound _ _ muNegFiveZeroFourOwner_check_s0
  · exact LRAT.check_sound _ _ muNegFiveZeroFourOwner_check_s1

theorem muNegFiveOneTwoOwner_unsat (sigma : Bool) :
    (muNegFiveOneTwoOwnerSatCnf sigma).Unsat := by
  cases sigma
  · exact LRAT.check_sound _ _ muNegFiveOneTwoOwner_check_s0
  · exact LRAT.check_sound _ _ muNegFiveOneTwoOwner_check_s1

end Erdos85

#print axioms Erdos85.muNegFiveZeroFourOwner_check_s0
#print axioms Erdos85.muNegFiveZeroFourOwner_check_s1
#print axioms Erdos85.muNegFiveOneTwoOwner_check_s0
#print axioms Erdos85.muNegFiveOneTwoOwner_check_s1
#print axioms Erdos85.muNegFiveZeroFourOwner_unsat
#print axioms Erdos85.muNegFiveOneTwoOwner_unsat
