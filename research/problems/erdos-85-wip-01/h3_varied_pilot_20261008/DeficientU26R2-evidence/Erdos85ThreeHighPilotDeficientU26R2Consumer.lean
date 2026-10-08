import Proofs.Erdos85ThreeHighPilotDeficientU26R2Certificate

namespace Erdos85.VariedPilot.DeficientU26R2
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R rejected cross hc he
end Erdos85.VariedPilot.DeficientU26R2
#print axioms Erdos85.VariedPilot.DeficientU26R2.no_joint
