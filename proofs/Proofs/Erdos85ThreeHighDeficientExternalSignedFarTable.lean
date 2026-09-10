import Proofs.Erdos85ThreeHighExternalSignedFarCertificate
import Proofs.Erdos85ThreeHighLowDegreePairGate
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate
import Proofs.Erdos85ThreeHighLowDegreePreflight

namespace Erdos85

def threeHighDeficientExternalSignedFarTable (i : Fin 13) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 9 15 0,
    threeBlockDeficientCompactCode 6 9 16 0,
    threeBlockDeficientCompactCode 6 10 1 0,
    threeBlockDeficientCompactCode 6 10 21 0,
    threeBlockDeficientCompactCode 9 10 59 4,
    threeBlockDeficientCompactCode 9 8 14 0,
    threeBlockDeficientCompactCode 9 13 80 1,
    threeBlockDeficientCompactCode 9 13 80 2,
    threeBlockDeficientCompactCode 9 13 104 0,
    threeBlockDeficientCompactCode 9 12 20 4,
    threeBlockDeficientCompactCode 9 12 58 4,
    threeBlockDeficientCompactCode 9 12 66 4,
    threeBlockDeficientCompactCode 9 12 82 1] i

def threeHighDeficientExternalSignedFarAdj (i : Fin 13) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientExternalSignedFarTable i))

def threeHighDeficientExternalSignedFarVertices (i : Fin 13) : Fin 5 → Fin 15 :=
  ![![4,5,9,10,13],
    ![4,5,9,10,13],
    ![4,5,9,10,12],
    ![4,5,9,10,12],
    ![4,8,9,10,12],
    ![4,5,8,10,11],
    ![4,6,8,10,11],
    ![4,7,8,10,12],
    ![4,5,8,10,14],
    ![4,8,9,10,13],
    ![4,8,9,10,13],
    ![4,8,9,10,13],
    ![4,6,8,10,11]] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientExternalSignedFarTable_injective :
    Function.Injective threeHighDeficientExternalSignedFarTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientExternalSignedFarTable_checked (i : Fin 13) :
    ThreeHighExternalSignedFarObstruction (threeHighDeficientExternalSignedFarAdj i)
      (threeHighDeficientExternalSignedFarVertices i) := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientExternalSignedFarTable_prior_filters (i : Fin 13) :
    let U := threeHighDeficientExternalSignedFarAdj i
    encodedC4Free U = true ∧ threeHighLowDegreeGate U = true ∧
      threeHighLowDegreeTriangleGate U = true ∧ threeHighLowDegreePairGate U = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDeficientExternalSignedFarTable_no_external_cross (i : Fin 13)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeHighDeficientExternalSignedFarAdj i) R)
    (hExt : encodedExternalBlockCap
      (threeHighEmptyAdj (threeHighDeficientExternalSignedFarAdj i) R cross) threeHighCanonicalRow = true) : False := by
  exact (threeHighDeficientExternalSignedFarTable_checked i).no_external_cross _ _ R h67 h76 cross hc hExt

end Erdos85
#print axioms Erdos85.threeHighDeficientExternalSignedFarTable_injective
#print axioms Erdos85.threeHighDeficientExternalSignedFarTable_checked
#print axioms Erdos85.threeHighDeficientExternalSignedFarTable_prior_filters
#print axioms Erdos85.threeHighDeficientExternalSignedFarTable_no_external_cross
