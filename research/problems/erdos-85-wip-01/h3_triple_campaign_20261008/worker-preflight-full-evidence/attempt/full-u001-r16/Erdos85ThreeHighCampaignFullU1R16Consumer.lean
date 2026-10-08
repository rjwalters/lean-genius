import Erdos85ThreeHighCampaignFullU1R16Membership
import Proofs.Erdos85ThreeHighCampaignFullU1R16Certificate
namespace Erdos85.TripleCampaign.FullU1R16
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem representative_rejected :
    threeHighNativePairSearch (FullURestrictedAssembly.representative 1)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16)) = false := by
  rw [input_identity]
  exact rejected
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative 1)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative 1)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative 1)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 16)) cross) :=
  threeHighNativePairSearch_no_joint _ _ representative_rejected cross hc he
end Erdos85.TripleCampaign.FullU1R16
#print axioms Erdos85.TripleCampaign.FullU1R16.representative_rejected
#print axioms Erdos85.TripleCampaign.FullU1R16.no_joint
