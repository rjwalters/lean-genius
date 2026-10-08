import CapacityReduction
import Proofs.Erdos85ThreeHighPilotFullU3R3Inputs
import Proofs.Erdos85ThreeHighPilotFullU54R20Inputs

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem FullU3R3_mem : (3,3) ∈ FullCapacityPruning.remainingPairs := by decide
theorem FullU3R3_input : FullURestrictedAssembly.representative 3 = Erdos85.VariedPilot.FullU3R3.U := by rfl
#print axioms FullU3R3_mem
#print axioms FullU3R3_input

theorem FullU54R20_mem : (54,20) ∈ FullCapacityPruning.remainingPairs := by decide
theorem FullU54R20_input : FullURestrictedAssembly.representative 54 = Erdos85.VariedPilot.FullU54R20.U := by rfl
#print axioms FullU54R20_mem
#print axioms FullU54R20_input
