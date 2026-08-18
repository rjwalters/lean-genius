import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncoding

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

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- First end-to-end generator audit. -/
theorem tenSixOutsideGeneratedCnf_zero_eq_parsed :
    tenSixOutsideGeneratedCnf 0 = tenSixC001Cnf := by
  apply cnf_eq_of_clauses_eq
  native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- All six formulas are reproduced exactly by the Lean generator. -/
theorem tenSixOutsideGeneratedCnf_eq_parsed (i : Fin 6) :
    tenSixOutsideGeneratedCnf i = tenSixOutsideParsedCnf i := by
  apply cnf_eq_of_clauses_eq
  fin_cases i <;> native_decide

end Erdos85
