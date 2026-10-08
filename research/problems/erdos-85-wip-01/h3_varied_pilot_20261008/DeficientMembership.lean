import Pruning
import Proofs.Erdos85ThreeHighPilotDeficientU26R2Inputs
import Proofs.Erdos85ThreeHighPilotDeficientU369R11Inputs

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem DeficientU26R2_mem : (26,2) ∈ DeficientUOrbitPruning.remainingPairs := by
  simp only [DeficientUOrbitPruning.remainingPairs, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem DeficientU26R2_input : DeficientUOrbitPruning.representative 26 = Erdos85.VariedPilot.DeficientU26R2.U := by rfl
#print axioms DeficientU26R2_mem
#print axioms DeficientU26R2_input

theorem DeficientU369R11_mem : (369,11) ∈ DeficientUOrbitPruning.remainingPairs := by
  simp only [DeficientUOrbitPruning.remainingPairs, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
  decide
theorem DeficientU369R11_input : DeficientUOrbitPruning.representative 369 = Erdos85.VariedPilot.DeficientU369R11.U := by rfl
#print axioms DeficientU369R11_mem
#print axioms DeficientU369R11_input
