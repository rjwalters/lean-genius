import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncodingAudit001
import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncodingAudit002
import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncodingAudit003
import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncodingAudit004
import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncodingAudit005
import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncodingAudit006

/-! # Large native audits for the six `[10,6]` outside-C formulas

Kept separate from the coordinate/generator definitions so semantic clients
do not replay seven 120k-clause computations merely to import the interface.
-/

namespace Erdos85

/-- The finite coordinate reconstruction agrees with all six parsed DIMACS
variable counts. -/
theorem tenSixOutsideParsed_numLiterals :
    tenSixC001Cnf.numLiterals = (tenSixOutsideAllowedPairs 0).size ∧
    tenSixC002Cnf.numLiterals = (tenSixOutsideAllowedPairs 1).size ∧
    tenSixC003Cnf.numLiterals = (tenSixOutsideAllowedPairs 2).size ∧
    tenSixC004Cnf.numLiterals = (tenSixOutsideAllowedPairs 3).size ∧
    tenSixC005Cnf.numLiterals = (tenSixOutsideAllowedPairs 4).size ∧
    tenSixC006Cnf.numLiterals = (tenSixOutsideAllowedPairs 5).size := by
  native_decide

/-- All six formulas are reproduced exactly by the Lean generator. -/
theorem tenSixOutsideGeneratedCnf_eq_parsed (i : Fin 6) :
    tenSixOutsideGeneratedCnf i = tenSixOutsideParsedCnf i := by
  fin_cases i
  · exact tenSixOutsideGeneratedCnf_001_eq_parsed
  · exact tenSixOutsideGeneratedCnf_002_eq_parsed
  · exact tenSixOutsideGeneratedCnf_003_eq_parsed
  · exact tenSixOutsideGeneratedCnf_004_eq_parsed
  · exact tenSixOutsideGeneratedCnf_005_eq_parsed
  · exact tenSixOutsideGeneratedCnf_006_eq_parsed

end Erdos85
