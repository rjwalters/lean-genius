import Proofs.Erdos85ThreeHighNativePairSearch
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

/-! Compiled-check pilot for one complete H3 U/R pair, not a stratum exclusion. -/

namespace Erdos85

namespace NativeTerminalPilot

def U : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeBlockCompactCode 6 6 15))

def R : Fin 8 → Fin 8 → Bool :=
  threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 15)

set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by
  native_decide

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R rejected cross hc he

end NativeTerminalPilot

end Erdos85

#print axioms Erdos85.NativeTerminalPilot.rejected
#print axioms Erdos85.NativeTerminalPilot.no_joint
