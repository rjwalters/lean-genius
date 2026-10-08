import Proofs.Erdos85ThreeHighNativePairSearch
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

/-! Isolated native rejection for the U1/R15 pilot; no consumer or stratum exclusion. -/

namespace Erdos85

namespace NativeTerminalPilot

def U : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))

def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 15)

set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by
  native_decide

end NativeTerminalPilot

end Erdos85

#print axioms Erdos85.NativeTerminalPilot.rejected
