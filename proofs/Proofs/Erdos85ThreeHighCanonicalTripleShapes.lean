import Proofs.Erdos85ThreeHighBlockResolution
import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalResolution

namespace Erdos85

def threeHighCanonicalTripleShapes (k : Fin 3) : List (Finset (Fin 24)) :=
  threeHighTripleList.filter fun S =>
    decide (S ⊆ threeHighCanonicalResidual k ∧ S.card = 3) &&
      encodedTripleBlockCap threeHighCanonicalRow S

def threeHighTripleNoCommonNeighbor (B : Fin 24 → Fin 24 → Bool)
    (S : Finset (Fin 24)) : Bool :=
  decide (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c, ¬ (B a c = true ∧ B b c = true))

theorem threeHighCanonicalTripleShapes_filter (B : Fin 24 → Fin 24 → Bool) (k : Fin 3) :
    (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B) =
      threeHighBlockTripleList B (threeHighCanonicalResidual k) threeHighCanonicalRow := by
  unfold threeHighCanonicalTripleShapes threeHighBlockTripleList threeHighDirectTripleList
  simp only [List.filter_filter]
  congr 1
  funext S
  by_cases hsub : S ⊆ threeHighCanonicalResidual k <;>
    by_cases hcard : S.card = 3 <;>
    simp [threeHighTripleEligible, threeHighTripleNoCommonNeighbor, hsub, hcard, Bool.and_comm]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem threeHighCanonicalTripleShapes_length (k : Fin 3) :
    (threeHighCanonicalTripleShapes k).length = 536 := by
  decide +revert

end Erdos85
#print axioms Erdos85.threeHighCanonicalTripleShapes_filter

#print axioms Erdos85.threeHighCanonicalTripleShapes_length
