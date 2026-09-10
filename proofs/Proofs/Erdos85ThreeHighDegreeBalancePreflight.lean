import Proofs.Erdos85ThreeHighDegreeBalance
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

def threeHighDegreeBalanceGate (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool) : Bool :=
  decide ((∑ i, encodedRowDegree (U i)) = (∑ j, encodedRowDegree (R j)) + 34)

/-- Reject incompatible total degree demands before invoking cross-edge search. -/
def threeHighDegreeBalancePreflight (search : ThreeHighExternalSearch) : ThreeHighExternalSearch :=
  fun U R accept => threeHighDegreeBalanceGate U R && search U R accept

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDegreeBalancePreflight_sound (search : ThreeHighExternalSearch)
    (hs : ThreeHighExternalSearchSound search) :
    ThreeHighExternalSearchSound (threeHighDegreeBalancePreflight search) := by
  intro U R accept cross hc hExt ha
  simp only [threeHighDegreeBalancePreflight,Bool.and_eq_true]
  exact ⟨decide_eq_true (threeHighCrossDomain_degree_balance U R cross hc),
    hs U R accept cross hc hExt ha⟩

theorem threeHighDegreeBalancePreflight_reject (search : ThreeHighExternalSearch)
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (accept : ThreeHighCross → Bool)
    (h : (∑ i, encodedRowDegree (U i)) ≠ (∑ j, encodedRowDegree (R j)) + 34) :
    threeHighDegreeBalancePreflight search U R accept = false := by
  simp [threeHighDegreeBalancePreflight,threeHighDegreeBalanceGate,h]

end Erdos85
#print axioms Erdos85.threeHighDegreeBalancePreflight_sound
#print axioms Erdos85.threeHighDegreeBalancePreflight_reject
