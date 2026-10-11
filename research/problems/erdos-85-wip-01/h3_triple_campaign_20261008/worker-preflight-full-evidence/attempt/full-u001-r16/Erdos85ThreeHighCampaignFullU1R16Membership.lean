import CapacityReduction
import Proofs.Erdos85ThreeHighCampaignFullU1R16Inputs
namespace Erdos85.TripleCampaign.FullU1R16
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem member : (1,16) ∈ FullCapacityPruning.remainingPairs := by
  simp only [FullCapacityPruning.remainingPairs, FullTerminalPruning.remainingPairs, FullUBlockPruning.remainingPairs, FullUOrbitPruning.remainingPairs, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem input_identity : FullURestrictedAssembly.representative 1 = U := by rfl
#print axioms Erdos85.TripleCampaign.FullU1R16.member
#print axioms Erdos85.TripleCampaign.FullU1R16.input_identity
end Erdos85.TripleCampaign.FullU1R16
