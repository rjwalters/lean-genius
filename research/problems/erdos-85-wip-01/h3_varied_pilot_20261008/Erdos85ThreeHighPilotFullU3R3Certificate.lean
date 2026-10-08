import Proofs.Erdos85ThreeHighPilotFullU3R3Inputs

/-! Unverified timing-sample rejection; no stratum exclusion. -/
namespace Erdos85.VariedPilot.FullU3R3
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end Erdos85.VariedPilot.FullU3R3
#print axioms Erdos85.VariedPilot.FullU3R3.rejected
