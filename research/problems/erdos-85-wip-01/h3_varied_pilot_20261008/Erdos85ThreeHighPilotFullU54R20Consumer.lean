import Proofs.Erdos85ThreeHighPilotFullU54R20Certificate

namespace Erdos85.VariedPilot.FullU54R20
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj U R cross) :=
  threeHighNativePairSearch_no_joint U R rejected cross hc he
end Erdos85.VariedPilot.FullU54R20
#print axioms Erdos85.VariedPilot.FullU54R20.no_joint
