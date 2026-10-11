import CapacityReduction
import Proofs.Erdos85ThreeHighCampaignFullU3R3Inputs
namespace Erdos85.TripleCampaign.FullU3R3
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem member : (3,3) ∈ FullCapacityPruning.remainingPairs := by
  simp only [FullCapacityPruning.remainingPairs, FullTerminalPruning.remainingPairs, FullUBlockPruning.remainingPairs, FullUOrbitPruning.remainingPairs, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem input_identity : FullURestrictedAssembly.representative 3 = U := by rfl
#print axioms Erdos85.TripleCampaign.FullU3R3.member
#print axioms Erdos85.TripleCampaign.FullU3R3.input_identity
end Erdos85.TripleCampaign.FullU3R3
