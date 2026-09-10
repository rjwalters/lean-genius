import Proofs.Erdos85ThreeHighFarColorCertificate
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighLowDegreePreflight
import Proofs.Erdos85ThreeHighLowDegreePairGate
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate

namespace Erdos85

def threeHighFullFarColorTable (i : Fin 14) : ThreeBlockFirstRowParameters :=
  ![threeBlockCompactCode 6 6 15,
    threeBlockCompactCode 6 6 16,
    threeBlockCompactCode 6 9 14,
    threeBlockCompactCode 6 9 20,
    threeBlockCompactCode 6 9 54,
    threeBlockCompactCode 6 9 55,
    threeBlockCompactCode 6 3 1,
    threeBlockCompactCode 6 10 0,
    threeBlockCompactCode 6 10 5,
    threeBlockCompactCode 6 10 54,
    threeBlockCompactCode 9 9 5,
    threeBlockCompactCode 9 9 21,
    threeBlockCompactCode 9 9 54,
    threeBlockCompactCode 9 4 0] i

def threeHighFullFarColorTableAdj (i : Fin 14) : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeHighFullFarColorTable i))

def threeHighFullFarColorVertices (i : Fin 14) : Fin 3 → Fin 15 :=
  ![![4,9,14],![4,9,14],![4,9,13],![4,9,13],![4,9,13],![4,9,13],![4,9,14],![4,9,12],![4,9,12],![4,9,12],![4,8,13],![4,8,13],![4,8,13],![4,8,13]] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullFarColorTable_injective :
    Function.Injective threeHighFullFarColorTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullFarColorTable_checked (i : Fin 14) :
    ThreeHighFarColorObstruction (threeHighFullFarColorTableAdj i) (threeHighFullFarColorVertices i) := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullFarColorTable_prior_filters (i : Fin 14) :
    encodedC4Free (threeHighFullFarColorTableAdj i) = true ∧
    threeHighLowDegreeGate (threeHighFullFarColorTableAdj i) = true ∧
    threeHighLowDegreeTriangleGate (threeHighFullFarColorTableAdj i) = true ∧
    threeHighLowDegreePairGate (threeHighFullFarColorTableAdj i) = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighFullFarColorTable_no_cross (i : Fin 14)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross) : cross ∉ threeHighCrossDomain (threeHighFullFarColorTableAdj i) R := by
  exact (threeHighFullFarColorTable_checked i).no_cross _ _ R h67 h76 cross

end Erdos85
#print axioms Erdos85.threeHighFullFarColorTable_injective
#print axioms Erdos85.threeHighFullFarColorTable_checked
#print axioms Erdos85.threeHighFullFarColorTable_prior_filters
#print axioms Erdos85.threeHighFullFarColorTable_no_cross
