import Proofs.Erdos85ThreeHighLowDegreePair
import Proofs.Erdos85ThreeHighLowDegreePreflight
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate

namespace Erdos85

/-- Explicit configurations surviving the previous filters but rejected by a low-degree pair. -/
def threeHighDeficientPairTable (i : Fin 41) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 6 15 3,
    threeBlockDeficientCompactCode 6 6 16 2,
    threeBlockDeficientCompactCode 6 9 5 3,
    threeBlockDeficientCompactCode 6 9 14 4,
    threeBlockDeficientCompactCode 6 9 21 3,
    threeBlockDeficientCompactCode 6 9 54 3,
    threeBlockDeficientCompactCode 6 9 54 4,
    threeBlockDeficientCompactCode 6 3 1 3,
    threeBlockDeficientCompactCode 6 10 0 2,
    threeBlockDeficientCompactCode 6 10 0 4,
    threeBlockDeficientCompactCode 6 10 21 2,
    threeBlockDeficientCompactCode 6 10 54 4,
    threeBlockDeficientCompactCode 9 9 3 2,
    threeBlockDeficientCompactCode 9 9 15 1,
    threeBlockDeficientCompactCode 9 9 15 3,
    threeBlockDeficientCompactCode 9 9 16 1,
    threeBlockDeficientCompactCode 9 9 17 3,
    threeBlockDeficientCompactCode 9 9 55 3,
    threeBlockDeficientCompactCode 9 9 56 2,
    threeBlockDeficientCompactCode 9 9 58 3,
    threeBlockDeficientCompactCode 9 9 58 4,
    threeBlockDeficientCompactCode 9 9 60 1,
    threeBlockDeficientCompactCode 9 9 82 0,
    threeBlockDeficientCompactCode 9 9 94 0,
    threeBlockDeficientCompactCode 9 10 1 2,
    threeBlockDeficientCompactCode 9 10 21 2,
    threeBlockDeficientCompactCode 9 10 54 3,
    threeBlockDeficientCompactCode 9 4 1 3,
    threeBlockDeficientCompactCode 9 4 14 1,
    threeBlockDeficientCompactCode 9 4 14 3,
    threeBlockDeficientCompactCode 9 7 0 2,
    threeBlockDeficientCompactCode 9 7 14 2,
    threeBlockDeficientCompactCode 9 8 0 1,
    threeBlockDeficientCompactCode 9 8 55 1,
    threeBlockDeficientCompactCode 9 13 0 0,
    threeBlockDeficientCompactCode 9 13 0 3,
    threeBlockDeficientCompactCode 9 13 1 0,
    threeBlockDeficientCompactCode 9 13 67 3,
    threeBlockDeficientCompactCode 9 12 5 0,
    threeBlockDeficientCompactCode 9 12 5 3,
    threeBlockDeficientCompactCode 9 12 14 0] i

def threeHighDeficientPairTableAdj (i : Fin 41) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientPairTable i))

def threeHighDeficientPairWitness (i : Fin 41) : Fin 15 × Fin 15 × Fin 15 :=
  ![(14,9,4),(14,9,4),(13,8,3),(9,14,4),(13,8,3),(13,8,3),(9,14,4),(14,9,4),(12,7,2),(9,14,4),(12,7,2),(9,14,4),(13,8,3),(13,8,3),(8,13,3),(13,8,3),(8,13,3),(8,13,3),(13,8,3),(8,13,3),(13,8,3),(13,8,3),(13,8,3),(13,8,3),(12,7,2),(12,7,2),(8,13,3),(8,13,3),(13,8,3),(8,13,3),(12,7,2),(12,7,2),(11,6,1),(11,6,1),(10,5,0),(8,13,3),(10,5,0),(8,13,3),(10,5,0),(8,13,3),(10,5,0)] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientPairTable_injective :
    Function.Injective threeHighDeficientPairTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientPairTable_checked (i : Fin 41) :
    let U := threeHighDeficientPairTableAdj i
    let w := threeHighDeficientPairWitness i
    w.1 ≠ w.2.1 ∧ encodedRowDegree (U w.1) ≤ 1 ∧
      encodedRowDegree (U w.2.1) ≤ 2 ∧ U w.1 w.2.2 = true ∧ U w.2.1 w.2.2 = true := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientPairTable_prior_filters (i : Fin 41) :
    encodedC4Free (threeHighDeficientPairTableAdj i) = true ∧
    threeHighLowDegreeGate (threeHighDeficientPairTableAdj i) = true ∧
    threeHighLowDegreeTriangleGate (threeHighDeficientPairTableAdj i) = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDeficientPairTable_no_cross (i : Fin 41)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain (threeHighDeficientPairTableAdj i) R := by
  intro hc
  obtain ⟨hxy,hx,hy,hxs,hys⟩ := threeHighDeficientPairTable_checked i
  exact threeHighCrossDomain_no_low_degree_pair _ R cross hc _ _ _ hxy hx hy hxs hys

end Erdos85
#print axioms Erdos85.threeHighDeficientPairTable_injective
#print axioms Erdos85.threeHighDeficientPairTable_checked
#print axioms Erdos85.threeHighDeficientPairTable_prior_filters
#print axioms Erdos85.threeHighDeficientPairTable_no_cross
