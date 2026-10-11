import Proofs.Erdos85ThreeHighPilotFullU54R20Inputs

/-! Unverified timing-sample rejection; no stratum exclusion. -/
namespace Erdos85.VariedPilot.FullU54R20
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end Erdos85.VariedPilot.FullU54R20
#print axioms Erdos85.VariedPilot.FullU54R20.rejected
