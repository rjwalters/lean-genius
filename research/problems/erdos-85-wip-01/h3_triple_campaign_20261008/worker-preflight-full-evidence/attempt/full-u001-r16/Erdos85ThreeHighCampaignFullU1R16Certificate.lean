import Proofs.Erdos85ThreeHighCampaignFullU1R16Inputs
namespace Erdos85.TripleCampaign.FullU1R16
open Erdos85
set_option maxRecDepth 100000 in
theorem rejected : threeHighNativePairSearch U R = false := by native_decide
end Erdos85.TripleCampaign.FullU1R16
#print axioms Erdos85.TripleCampaign.FullU1R16.rejected
