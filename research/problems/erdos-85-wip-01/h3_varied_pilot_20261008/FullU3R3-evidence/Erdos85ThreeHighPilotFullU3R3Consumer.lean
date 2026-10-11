import Proofs.Erdos85ThreeHighPilotFullU3R3Certificate

namespace Erdos85.VariedPilot.FullU3R3
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R rejected cross hc he
end Erdos85.VariedPilot.FullU3R3
#print axioms Erdos85.VariedPilot.FullU3R3.no_joint
