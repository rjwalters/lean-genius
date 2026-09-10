import Proofs.Erdos85ThreeHighFarColorCertificate
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighLowDegreePreflight
import Proofs.Erdos85ThreeHighLowDegreePairGate
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate

namespace Erdos85

def threeHighDeficientFarColorTable (i : Fin 89) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 6 1 1,
    threeBlockDeficientCompactCode 6 6 1 2,
    threeBlockDeficientCompactCode 6 6 3 2,
    threeBlockDeficientCompactCode 6 6 10 1,
    threeBlockDeficientCompactCode 6 6 15 0,
    threeBlockDeficientCompactCode 6 6 15 1,
    threeBlockDeficientCompactCode 6 6 16 0,
    threeBlockDeficientCompactCode 6 6 16 1,
    threeBlockDeficientCompactCode 6 6 17 3,
    threeBlockDeficientCompactCode 6 6 61 1,
    threeBlockDeficientCompactCode 6 6 61 2,
    threeBlockDeficientCompactCode 6 6 63 2,
    threeBlockDeficientCompactCode 6 9 0 1,
    threeBlockDeficientCompactCode 6 9 0 2,
    threeBlockDeficientCompactCode 6 9 4 3,
    threeBlockDeficientCompactCode 6 9 5 2,
    threeBlockDeficientCompactCode 6 9 10 1,
    threeBlockDeficientCompactCode 6 9 14 1,
    threeBlockDeficientCompactCode 6 9 14 2,
    threeBlockDeficientCompactCode 6 9 14 3,
    threeBlockDeficientCompactCode 6 9 15 3,
    threeBlockDeficientCompactCode 6 9 16 2,
    threeBlockDeficientCompactCode 6 9 20 0,
    threeBlockDeficientCompactCode 6 9 20 1,
    threeBlockDeficientCompactCode 6 9 20 2,
    threeBlockDeficientCompactCode 6 9 20 3,
    threeBlockDeficientCompactCode 6 9 21 1,
    threeBlockDeficientCompactCode 6 9 54 0,
    threeBlockDeficientCompactCode 6 9 54 1,
    threeBlockDeficientCompactCode 6 9 55 0,
    threeBlockDeficientCompactCode 6 9 55 1,
    threeBlockDeficientCompactCode 6 9 55 2,
    threeBlockDeficientCompactCode 6 9 55 3,
    threeBlockDeficientCompactCode 6 9 58 3,
    threeBlockDeficientCompactCode 6 9 60 0,
    threeBlockDeficientCompactCode 6 9 60 3,
    threeBlockDeficientCompactCode 6 9 61 3,
    threeBlockDeficientCompactCode 6 9 67 1,
    threeBlockDeficientCompactCode 6 9 103 0,
    threeBlockDeficientCompactCode 6 9 114 0,
    threeBlockDeficientCompactCode 6 3 1 0,
    threeBlockDeficientCompactCode 6 3 1 2,
    threeBlockDeficientCompactCode 6 3 3 2,
    threeBlockDeficientCompactCode 6 3 11 1,
    threeBlockDeficientCompactCode 6 10 0 1,
    threeBlockDeficientCompactCode 6 10 0 3,
    threeBlockDeficientCompactCode 6 10 1 3,
    threeBlockDeficientCompactCode 6 10 5 0,
    threeBlockDeficientCompactCode 6 10 5 1,
    threeBlockDeficientCompactCode 6 10 5 2,
    threeBlockDeficientCompactCode 6 10 5 3,
    threeBlockDeficientCompactCode 6 10 19 2,
    threeBlockDeficientCompactCode 6 10 21 1,
    threeBlockDeficientCompactCode 6 10 54 0,
    threeBlockDeficientCompactCode 6 10 54 1,
    threeBlockDeficientCompactCode 6 10 54 3,
    threeBlockDeficientCompactCode 6 10 55 3,
    threeBlockDeficientCompactCode 6 10 67 1,
    threeBlockDeficientCompactCode 6 10 79 0,
    threeBlockDeficientCompactCode 6 10 103 0,
    threeBlockDeficientCompactCode 9 9 5 1,
    threeBlockDeficientCompactCode 9 9 5 2,
    threeBlockDeficientCompactCode 9 9 11 1,
    threeBlockDeficientCompactCode 9 9 14 4,
    threeBlockDeficientCompactCode 9 9 21 1,
    threeBlockDeficientCompactCode 9 9 21 2,
    threeBlockDeficientCompactCode 9 9 54 0,
    threeBlockDeficientCompactCode 9 9 54 1,
    threeBlockDeficientCompactCode 9 9 54 4,
    threeBlockDeficientCompactCode 9 9 58 2,
    threeBlockDeficientCompactCode 9 9 59 4,
    threeBlockDeficientCompactCode 9 9 60 4,
    threeBlockDeficientCompactCode 9 10 0 4,
    threeBlockDeficientCompactCode 9 10 54 4,
    threeBlockDeficientCompactCode 9 4 0 0,
    threeBlockDeficientCompactCode 9 4 0 2,
    threeBlockDeficientCompactCode 9 4 0 4,
    threeBlockDeficientCompactCode 9 4 14 4,
    threeBlockDeficientCompactCode 9 4 20 1,
    threeBlockDeficientCompactCode 9 7 0 4,
    threeBlockDeficientCompactCode 9 7 14 4,
    threeBlockDeficientCompactCode 9 8 0 4,
    threeBlockDeficientCompactCode 9 8 14 4,
    threeBlockDeficientCompactCode 9 8 54 4,
    threeBlockDeficientCompactCode 9 13 0 4,
    threeBlockDeficientCompactCode 9 13 54 4,
    threeBlockDeficientCompactCode 9 13 80 4,
    threeBlockDeficientCompactCode 9 12 14 4,
    threeBlockDeficientCompactCode 9 12 60 4] i

def threeHighDeficientFarColorTableAdj (i : Fin 89) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientFarColorTable i))

/-- Repeated padding labels do not require extra coverage or injectivity assumptions. -/
def threeHighDeficientFarColorVertices (i : Fin 89) : Fin 5 → Fin 15 :=
  ![![4,6,9,11,14],![4,7,9,12,14],![4,7,9,13,14],![4,6,9,12,14],![4,5,9,10,14],![4,6,9,13,14],![4,5,9,10,14],![4,6,9,13,14],![4,8,9,12,14],![4,6,9,13,14],![4,7,9,10,14],![4,7,9,11,14],![4,6,9,11,13],![4,7,9,12,13],![4,8,9,12,13],![4,7,9,13,14],![4,6,9,12,13],![4,6,9,13,13],![4,7,9,12,13],![4,8,9,11,13],![4,8,9,13,14],![4,7,9,13,14],![4,5,9,10,13],![4,6,9,13,14],![4,7,9,12,13],![4,8,9,11,13],![4,6,9,13,14],![4,5,9,12,13],![4,6,9,11,13],![4,5,9,12,13],![4,6,9,11,13],![4,7,9,10,13],![4,8,9,13,14],![4,8,9,10,13],![4,5,9,12,13],![4,8,9,11,13],![4,8,9,13,14],![4,6,9,13,14],![4,5,9,13,14],![4,5,9,13,14],![4,5,9,10,14],![4,7,9,12,14],![4,7,9,13,14],![4,6,9,12,14],![4,6,9,11,12],![4,8,9,12,13],![4,8,9,12,14],![4,5,9,10,12],![4,6,9,11,12],![4,7,9,12,14],![4,8,9,12,13],![4,7,9,11,12],![4,6,9,12,14],![4,5,9,12,12],![4,6,9,11,12],![4,8,9,12,13],![4,8,9,12,14],![4,6,9,12,14],![4,5,9,12,13],![4,5,9,12,14],![4,6,8,11,13],![4,7,8,13,14],![4,6,8,12,13],![4,8,9,13,14],![4,6,8,13,14],![4,7,8,12,13],![4,5,8,12,13],![4,6,8,11,13],![4,8,9,13,14],![4,7,8,13,14],![4,8,9,10,13],![4,8,9,13,14],![4,8,9,12,14],![4,8,9,12,14],![4,5,8,10,13],![4,7,8,12,13],![4,8,9,13,14],![4,8,9,13,14],![4,6,8,13,14],![4,8,9,12,14],![4,8,9,12,14],![4,8,9,11,14],![4,8,9,11,14],![4,8,9,11,14],![4,8,9,10,14],![4,8,9,10,14],![4,8,9,10,14],![4,8,9,10,14],![4,8,9,10,14]] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem threeHighDeficientFarColorTable_injective :
    Function.Injective threeHighDeficientFarColorTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem threeHighDeficientFarColorTable_checked (i : Fin 89) :
    ThreeHighFarColorObstruction (threeHighDeficientFarColorTableAdj i) (threeHighDeficientFarColorVertices i) := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem threeHighDeficientFarColorTable_prior_filters (i : Fin 89) :
    encodedC4Free (threeHighDeficientFarColorTableAdj i) = true ∧
    threeHighLowDegreeGate (threeHighDeficientFarColorTableAdj i) = true ∧
    threeHighLowDegreeTriangleGate (threeHighDeficientFarColorTableAdj i) = true ∧
    threeHighLowDegreePairGate (threeHighDeficientFarColorTableAdj i) = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDeficientFarColorTable_no_cross (i : Fin 89)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross) : cross ∉ threeHighCrossDomain (threeHighDeficientFarColorTableAdj i) R := by
  exact (threeHighDeficientFarColorTable_checked i).no_cross _ _ R h67 h76 cross

end Erdos85
#print axioms Erdos85.threeHighDeficientFarColorTable_injective
#print axioms Erdos85.threeHighDeficientFarColorTable_checked
#print axioms Erdos85.threeHighDeficientFarColorTable_prior_filters
#print axioms Erdos85.threeHighDeficientFarColorTable_no_cross
