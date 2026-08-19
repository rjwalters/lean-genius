import Proofs.Erdos85OrderSixtyFourTenSixOutsideEncoding

namespace Erdos85

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixOutsideGeneratedCnf_002_eq_parsed :
    tenSixOutsideGeneratedCnf 1 = tenSixC002Cnf := by
  apply cnf_eq_of_clauses_eq
  native_decide

end Erdos85
