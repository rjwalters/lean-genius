import Proofs.Erdos85ThreeHighPilotDeficientU369R11Inputs

/-! Unverified timing-sample rejection; no stratum exclusion. -/
namespace Erdos85.VariedPilot.DeficientU369R11
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end Erdos85.VariedPilot.DeficientU369R11
#print axioms Erdos85.VariedPilot.DeficientU369R11.rejected
