import Erdos85ThreeHighCampaignDeficientU0R2Membership
import Proofs.Erdos85ThreeHighCampaignDeficientU0R2Certificate
namespace Erdos85.TripleCampaign.DeficientU0R2
open Erdos85
attribute [local irreducible] threeHighCrossDomain
theorem representative_rejected :
    threeHighNativePairSearch (DeficientUNormalizedAssembly.representative 0)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 2)) = false := by
  rw [input_identity]
  exact rejected
theorem no_joint (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (DeficientUNormalizedAssembly.representative 0)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 2)))
    (he : encodedExternalBlockCap (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative 0)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 2)) cross)
      threeHighCanonicalRow = true) :
    ¬ ThreeHighDistinctJointWitness (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative 0)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative 2)) cross) :=
  threeHighNativePairSearch_no_joint _ _ representative_rejected cross hc he
end Erdos85.TripleCampaign.DeficientU0R2
#print axioms Erdos85.TripleCampaign.DeficientU0R2.representative_rejected
#print axioms Erdos85.TripleCampaign.DeficientU0R2.no_joint
