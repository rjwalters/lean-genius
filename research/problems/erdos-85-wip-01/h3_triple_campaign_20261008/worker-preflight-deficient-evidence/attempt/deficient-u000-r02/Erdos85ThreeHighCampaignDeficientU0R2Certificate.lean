import Proofs.Erdos85ThreeHighCampaignDeficientU0R2Inputs
namespace Erdos85.TripleCampaign.DeficientU0R2
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end Erdos85.TripleCampaign.DeficientU0R2
#print axioms Erdos85.TripleCampaign.DeficientU0R2.rejected
