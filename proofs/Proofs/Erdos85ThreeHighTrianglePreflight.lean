import Proofs.Erdos85ThreeHighLowDegreeTriangleGate
import Proofs.Erdos85ThreeHighExternalSearchCertificate
import Proofs.Erdos85ThreeHighFullTriangleExample

namespace Erdos85

/-- Reject the fixed U obstruction before invoking any cross-edge search. -/
def threeHighTrianglePreflight (search : ThreeHighExternalSearch) : ThreeHighExternalSearch :=
  fun U R accept => threeHighLowDegreeTriangleGate U && search U R accept

attribute [local irreducible] threeHighCrossDomain

theorem threeHighTrianglePreflight_sound (search : ThreeHighExternalSearch)
    (hs : ThreeHighExternalSearchSound search) :
    ThreeHighExternalSearchSound (threeHighTrianglePreflight search) := by
  intro U R accept cross hc hExt ha
  simp only [threeHighTrianglePreflight, Bool.and_eq_true]
  exact ⟨threeHighLowDegreeTriangleGate_of_cross U R cross hc, hs U R accept cross hc hExt ha⟩

set_option maxRecDepth 100000 in
theorem threeHighFullTriangleExample_gate_false :
    threeHighLowDegreeTriangleGate threeHighFullTriangleExampleAdj = false := by decide

/-- The old timed-out fixture is rejected before any downstream search is evaluated. -/
theorem threeHighTrianglePreflight_example_reject (search : ThreeHighExternalSearch)
    (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) :
    threeHighTrianglePreflight search threeHighFullTriangleExampleAdj R accept = false := by
  simp only [threeHighTrianglePreflight,threeHighFullTriangleExample_gate_false,Bool.false_and]

end Erdos85
#print axioms Erdos85.threeHighTrianglePreflight_sound

#print axioms Erdos85.threeHighFullTriangleExample_gate_false
#print axioms Erdos85.threeHighTrianglePreflight_example_reject
