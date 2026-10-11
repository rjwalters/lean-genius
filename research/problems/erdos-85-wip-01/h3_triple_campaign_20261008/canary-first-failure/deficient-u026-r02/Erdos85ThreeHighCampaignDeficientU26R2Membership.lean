import Pruning
import Proofs.Erdos85ThreeHighCampaignDeficientU26R2Inputs
namespace Erdos85.TripleCampaign.DeficientU26R2
open Erdos85
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem member : (26,2) ∈ DeficientUOrbitPruning.remainingPairs := by
  simp only [DeficientUOrbitPruning.remainingPairs, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem input_identity : DeficientUNormalizedAssembly.representative 26 = U := by rfl
#print axioms Erdos85.TripleCampaign.DeficientU26R2.member
#print axioms Erdos85.TripleCampaign.DeficientU26R2.input_identity
end Erdos85.TripleCampaign.DeficientU26R2
