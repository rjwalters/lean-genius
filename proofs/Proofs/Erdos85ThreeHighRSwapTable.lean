import Proofs.Erdos85ThreeHighRSwapOrdering
import Proofs.Erdos85ThreeHighSecondaryOrbitTable

namespace Erdos85
/-- Disjoint near/far-preserving swap automorphisms for each secondary representative.
The table need not contain every automorphism. -/
def threeHighSecondarySwapPairs : Fin 21 → List (Fin 8 × Fin 8) :=
  ![[(2,3),(4,5)],
    [(0,1),(3,4)],
    [(2,3),(4,5),(6,7)],
    [(2,3),(4,5),(6,7)],
    [(2,3),(4,5)],
    [(3,4)],
    [(3,4)],
    [(0,1),(3,4),(6,7)],
    [(0,1),(3,4),(6,7)],
    [(0,1),(4,5)],
    [(0,1),(4,5)],
    [(0,1),(2,3),(4,5),(6,7)],
    [(2,3),(4,5)],
    [(0,1),(2,3)],
    [(2,3),(4,5),(6,7)],
    [(2,3),(4,5)],
    [(4,5)],
    [(2,3)],
    [(0,1),(2,3),(6,7)],
    [(0,1),(2,3)],
    [(0,1),(2,3),(4,5),(6,7)]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem threeHighSecondarySwapPairs_checked (q : Fin 21) :
    (threeHighSecondarySwapPairs q).Pairwise (fun p r =>
      p.1 ≠ r.1 ∧ p.1 ≠ r.2 ∧ p.2 ≠ r.1 ∧ p.2 ≠ r.2) ∧
    (∀ p ∈ threeHighSecondarySwapPairs q, p.1 < p.2) ∧
    (∀ p ∈ threeHighSecondarySwapPairs q, ∀ j,
      (Equiv.swap p.1 p.2 j).val < 6 ↔ j.val < 6) ∧
    (∀ p ∈ threeHighSecondarySwapPairs q, ∀ i j,
      threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)
        (Equiv.swap p.1 p.2 i) (Equiv.swap p.1 p.2 j) =
      threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q) i j) := by
  refine ⟨?_,?_,?_,?_⟩ <;> decide +revert

end Erdos85
#print axioms Erdos85.threeHighSecondarySwapPairs_checked
