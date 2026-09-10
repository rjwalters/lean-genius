import Proofs.Erdos85ThreeHighExternalFarCertificate
import Proofs.Erdos85ThreeHighLowDegreePairGate
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate
import Proofs.Erdos85ThreeHighLowDegreePreflight

namespace Erdos85

def threeHighDeficientExternalFarTable (i : Fin 51) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 6 10 1,
    threeBlockDeficientCompactCode 6 6 15 0,
    threeBlockDeficientCompactCode 6 6 16 1,
    threeBlockDeficientCompactCode 6 6 17 3,
    threeBlockDeficientCompactCode 6 9 5 0,
    threeBlockDeficientCompactCode 6 9 5 1,
    threeBlockDeficientCompactCode 6 9 14 2,
    threeBlockDeficientCompactCode 6 9 20 0,
    threeBlockDeficientCompactCode 6 9 21 0,
    threeBlockDeficientCompactCode 6 9 21 2,
    threeBlockDeficientCompactCode 6 9 55 2,
    threeBlockDeficientCompactCode 6 9 58 3,
    threeBlockDeficientCompactCode 6 3 1 0,
    threeBlockDeficientCompactCode 6 3 11 1,
    threeBlockDeficientCompactCode 6 10 0 1,
    threeBlockDeficientCompactCode 6 10 5 0,
    threeBlockDeficientCompactCode 6 10 21 3,
    threeBlockDeficientCompactCode 6 10 54 3,
    threeBlockDeficientCompactCode 6 10 55 1,
    threeBlockDeficientCompactCode 9 9 10 1,
    threeBlockDeficientCompactCode 9 9 15 2,
    threeBlockDeficientCompactCode 9 9 16 2,
    threeBlockDeficientCompactCode 9 9 37 0,
    threeBlockDeficientCompactCode 9 9 58 2,
    threeBlockDeficientCompactCode 9 9 60 0,
    threeBlockDeficientCompactCode 9 9 61 0,
    threeBlockDeficientCompactCode 9 9 62 2,
    threeBlockDeficientCompactCode 9 9 82 2,
    threeBlockDeficientCompactCode 9 9 94 1,
    threeBlockDeficientCompactCode 9 9 95 4,
    threeBlockDeficientCompactCode 9 10 1 1,
    threeBlockDeficientCompactCode 9 10 54 1,
    threeBlockDeficientCompactCode 9 10 54 4,
    threeBlockDeficientCompactCode 9 10 55 0,
    threeBlockDeficientCompactCode 9 10 79 1,
    threeBlockDeficientCompactCode 9 4 14 2,
    threeBlockDeficientCompactCode 9 4 14 4,
    threeBlockDeficientCompactCode 9 4 20 1,
    threeBlockDeficientCompactCode 9 4 38 0,
    threeBlockDeficientCompactCode 9 4 40 0,
    threeBlockDeficientCompactCode 9 7 0 0,
    threeBlockDeficientCompactCode 9 7 1 0,
    threeBlockDeficientCompactCode 9 7 14 4,
    threeBlockDeficientCompactCode 9 7 16 3,
    threeBlockDeficientCompactCode 9 8 0 0,
    threeBlockDeficientCompactCode 9 8 1 0,
    threeBlockDeficientCompactCode 9 13 0 1,
    threeBlockDeficientCompactCode 9 13 0 4,
    threeBlockDeficientCompactCode 9 13 55 1,
    threeBlockDeficientCompactCode 9 12 14 2,
    threeBlockDeficientCompactCode 9 12 14 4] i

def threeHighDeficientExternalFarAdj (i : Fin 51) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientExternalFarTable i))

def threeHighDeficientExternalFarVertices (i : Fin 51) : Fin 5 → Fin 15 :=
  ![![6,9,14,14,14],
    ![5,9,14,14,14],
    ![6,9,14,14,14],
    ![9,12,14,14,14],
    ![5,10,13,13,13],
    ![6,9,11,11,11],
    ![7,12,13,13,13],
    ![4,10,13,13,13],
    ![5,10,13,13,13],
    ![7,9,12,12,12],
    ![4,10,13,13,13],
    ![4,10,13,13,13],
    ![5,9,14,14,14],
    ![6,9,14,14,14],
    ![6,11,12,12,12],
    ![4,10,12,12,12],
    ![8,9,13,13,13],
    ![8,12,13,13,13],
    ![6,9,11,11,11],
    ![8,12,13,13,13],
    ![7,8,13,13,13],
    ![7,8,13,13,13],
    ![4,5,8,8,8],
    ![8,13,14,14,14],
    ![8,12,13,13,13],
    ![4,5,8,8,8],
    ![7,8,13,13,13],
    ![8,13,14,14,14],
    ![8,13,14,14,14],
    ![8,9,13,13,13],
    ![6,11,12,12,12],
    ![6,8,11,11,11],
    ![9,12,14,14,14],
    ![4,5,8,8,8],
    ![4,6,8,11,12],
    ![7,8,13,13,13],
    ![8,9,14,14,14],
    ![8,13,14,14,14],
    ![4,5,8,11,13],
    ![4,5,8,11,13],
    ![5,8,10,10,10],
    ![4,5,8,8,8],
    ![8,9,14,14,14],
    ![4,11,12,12,12],
    ![5,8,10,10,10],
    ![4,5,8,8,8],
    ![6,8,11,11,11],
    ![9,10,14,14,14],
    ![6,10,11,11,11],
    ![7,8,12,12,12],
    ![9,10,14,14,14]] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientExternalFarTable_injective :
    Function.Injective threeHighDeficientExternalFarTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientExternalFarTable_checked (i : Fin 51) :
    ThreeHighExternalFarObstruction (threeHighDeficientExternalFarAdj i)
      (threeHighDeficientExternalFarVertices i) := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientExternalFarTable_prior_filters (i : Fin 51) :
    let U := threeHighDeficientExternalFarAdj i
    encodedC4Free U = true ∧ threeHighLowDegreeGate U = true ∧
      threeHighLowDegreeTriangleGate U = true ∧ threeHighLowDegreePairGate U = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDeficientExternalFarTable_no_external_cross (i : Fin 51)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeHighDeficientExternalFarAdj i) R)
    (hExt : encodedExternalBlockCap
      (threeHighEmptyAdj (threeHighDeficientExternalFarAdj i) R cross) threeHighCanonicalRow = true) : False := by
  exact (threeHighDeficientExternalFarTable_checked i).no_external_cross _ _ R cross hc hExt

end Erdos85
#print axioms Erdos85.threeHighDeficientExternalFarTable_injective
#print axioms Erdos85.threeHighDeficientExternalFarTable_checked
#print axioms Erdos85.threeHighDeficientExternalFarTable_prior_filters
#print axioms Erdos85.threeHighDeficientExternalFarTable_no_external_cross
