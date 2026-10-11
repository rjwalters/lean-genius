import Proofs.Erdos85ThreeHighPilotDeficientU26R2Inputs

/-! Unverified timing-sample rejection; no stratum exclusion. -/
namespace Erdos85.VariedPilot.DeficientU26R2
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end Erdos85.VariedPilot.DeficientU26R2
#print axioms Erdos85.VariedPilot.DeficientU26R2.rejected
