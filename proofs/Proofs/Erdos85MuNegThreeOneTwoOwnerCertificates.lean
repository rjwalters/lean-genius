import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateFwdC0
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateFwdC2
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateFwdC4
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateFwdC6
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateRevC0
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateRevC2
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateRevC4
import Proofs.Erdos85MuNegThreeOneTwoOwnerCertificateRevC6

/-! A uniform interface to the eight independently compiled LRAT terminals. -/

namespace Erdos85

open Std.Tactic.BVDecide

theorem muNegThreeOneTwoOwner_check (fwd : Bool) (c : Nat)
    (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6) :
    LRAT.check
      (if fwd then
        if c = 0 then muNegThreeFwdC0Proof
        else if c = 2 then muNegThreeFwdC2Proof
        else if c = 4 then muNegThreeFwdC4Proof
        else muNegThreeFwdC6Proof
      else
        if c = 0 then muNegThreeRevC0Proof
        else if c = 2 then muNegThreeRevC2Proof
        else if c = 4 then muNegThreeRevC4Proof
        else muNegThreeRevC6Proof)
      (muNegThreeOneTwoOwnerSatCnf fwd c) := by
  rcases hc with rfl | rfl | rfl | rfl
  · cases fwd
    · simpa using muNegThreeOneTwoOwner_check_rev_c0
    · simpa using muNegThreeOneTwoOwner_check_fwd_c0
  · cases fwd
    · simpa using muNegThreeOneTwoOwner_check_rev_c2
    · simpa using muNegThreeOneTwoOwner_check_fwd_c2
  · cases fwd
    · simpa using muNegThreeOneTwoOwner_check_rev_c4
    · simpa using muNegThreeOneTwoOwner_check_fwd_c4
  · cases fwd
    · simpa using muNegThreeOneTwoOwner_check_rev_c6
    · simpa using muNegThreeOneTwoOwner_check_fwd_c6

/-- Every fixed-phase owner CNF in the eight-case family is unsatisfiable. -/
theorem muNegThreeOneTwoOwnerSatCnf_unsat (fwd : Bool) (c : Nat)
    (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6) :
    (muNegThreeOneTwoOwnerSatCnf fwd c).Unsat := by
  rcases hc with rfl | rfl | rfl | rfl
  · cases fwd
    · exact LRAT.check_sound muNegThreeRevC0Proof _ muNegThreeOneTwoOwner_check_rev_c0
    · exact LRAT.check_sound muNegThreeFwdC0Proof _ muNegThreeOneTwoOwner_check_fwd_c0
  · cases fwd
    · exact LRAT.check_sound muNegThreeRevC2Proof _ muNegThreeOneTwoOwner_check_rev_c2
    · exact LRAT.check_sound muNegThreeFwdC2Proof _ muNegThreeOneTwoOwner_check_fwd_c2
  · cases fwd
    · exact LRAT.check_sound muNegThreeRevC4Proof _ muNegThreeOneTwoOwner_check_rev_c4
    · exact LRAT.check_sound muNegThreeFwdC4Proof _ muNegThreeOneTwoOwner_check_fwd_c4
  · cases fwd
    · exact LRAT.check_sound muNegThreeRevC6Proof _ muNegThreeOneTwoOwner_check_rev_c6
    · exact LRAT.check_sound muNegThreeFwdC6Proof _ muNegThreeOneTwoOwner_check_fwd_c6

end Erdos85

#print axioms Erdos85.muNegThreeOneTwoOwnerSatCnf_unsat
