import Proofs.Erdos85ThreeHighDeficientPairTable
import Proofs.Erdos85ThreeHighLowDegreePairGate

namespace Erdos85

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientPairTable_gate_false (i : Fin 41) :
    threeHighLowDegreePairGate (threeHighDeficientPairTableAdj i) = false := by
  decide +revert

/-- All forty-one additional cases reject before any downstream search. -/
theorem threeHighDeficientPairTable_search_false (search : ThreeHighExternalSearch)
    (i : Fin 41) (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) :
    threeHighPairPreflight search (threeHighDeficientPairTableAdj i) R accept = false := by
  simp only [threeHighPairPreflight,threeHighDeficientPairTable_gate_false,Bool.false_and]

end Erdos85
#print axioms Erdos85.threeHighDeficientPairTable_gate_false
#print axioms Erdos85.threeHighDeficientPairTable_search_false
