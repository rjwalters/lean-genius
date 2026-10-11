import Erdos85ThreeHighCampaignFullU3R3Membership
import Proofs.Erdos85ThreeHighCampaignFullU3R3Certificate
namespace Erdos85.TripleCampaign.FullU3R3
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem representative_rejected :
    threeHighNativePairSearch (FullURestrictedAssembly.representative 3)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) = false := by
  rw [input_identity]
  exact rejected
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative 3)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative 3)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative 3)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 3)) cross) :=
  threeHighNativePairSearch_no_joint _ _ representative_rejected cross hc he
end Erdos85.TripleCampaign.FullU3R3
#print axioms Erdos85.TripleCampaign.FullU3R3.representative_rejected
#print axioms Erdos85.TripleCampaign.FullU3R3.no_joint
