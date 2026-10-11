import Proofs.Erdos85ThreeHighNativeTerminalPilotCertificate

/-! Consumer of the separately compiled U1/R15 rejection. -/

namespace Erdos85
namespace NativeTerminalPilot

attribute [local irreducible] threeHighCrossDomain

theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R rejected cross hc he

end NativeTerminalPilot
end Erdos85

#print axioms Erdos85.NativeTerminalPilot.no_joint
