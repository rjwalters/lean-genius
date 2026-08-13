import Proofs.Erdos85OneHighFamilyCnfGenerator

/-! Production-size native checks are isolated here so ordinary development
of later generator segments does not repeatedly evaluate a half-million-clause
prefix. -/

namespace Erdos85

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem oneHighFamilyC4Clauses_reference :
    let out := oneHighFamilyC4Clauses 4
    out.top = 780 ∧ out.ids.length = 780 ∧ out.clauses.size = 495320 := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem oneHighFamilyAtMostOneBlockClauses_reference :
    let out := oneHighFamilyAtMostOneBlockClauses 4
    out.top = 780 ∧ out.ids.length = 780 ∧ out.clauses.size = 497960 := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem oneHighFamilyFarDegreeClauses_AAAA_reference :
    let out := oneHighFamilyFarDegreeClauses 4
    out.top = 11388 ∧ out.ids.length = 780 ∧ out.clauses.size = 519176 := by
  native_decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem oneHighFamilyLexClauses_AAAA_reference :
    let out := oneHighFamilyLexClauses 4
    out.top = 11532 ∧ out.ids.length = 924 ∧ out.clauses.size = 520280 := by
  native_decide

end Erdos85
