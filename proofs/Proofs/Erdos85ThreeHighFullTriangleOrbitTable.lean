import Proofs.Erdos85ThreeHighOrbitRejection
import Proofs.Erdos85ThreeBlockCompactCodes

namespace Erdos85
/-- Twenty-two explicit full configurations; this table does not assert exhaustive source coverage. -/
def threeHighFullTriangleOrbitTable (i : Fin 22) : ThreeBlockFirstRowParameters :=
  ![threeBlockCompactCode 3 3 6,
    threeBlockCompactCode 3 3 80,
    threeBlockCompactCode 3 6 0,
    threeBlockCompactCode 4 4 7,
    threeBlockCompactCode 4 9 1,
    threeBlockCompactCode 5 5 94,
    threeBlockCompactCode 5 8 21,
    threeBlockCompactCode 6 3 0,
    threeBlockCompactCode 6 6 14,
    threeBlockCompactCode 6 6 54,
    threeBlockCompactCode 7 7 16,
    threeBlockCompactCode 7 10 5,
    threeBlockCompactCode 8 5 21,
    threeBlockCompactCode 8 8 67,
    threeBlockCompactCode 9 4 1,
    threeBlockCompactCode 9 9 55,
    threeBlockCompactCode 10 7 5,
    threeBlockCompactCode 10 10 82,
    threeBlockCompactCode 12 12 119,
    threeBlockCompactCode 12 13 105,
    threeBlockCompactCode 13 12 105,
    threeBlockCompactCode 13 13 111] i

def threeHighFullTriangleOrbitTableAdj (i : Fin 22) : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeHighFullTriangleOrbitTable i))

def threeHighFullTriangleOrbitCert (i : Fin 22) : ThreeBlockOrbitCertificate 4 :=
  ![.orbit 0 2 false,
    .orbit 0 24 false,
    .orbit 1 0 true,
    .orbit 2 24 false,
    .orbit 3 0 true,
    .orbit 2 62 false,
    .orbit 3 60 true,
    .orbit 1 0 false,
    .orbit 0 0 false,
    .orbit 0 26 false,
    .orbit 2 26 false,
    .orbit 3 2 true,
    .orbit 3 60 false,
    .orbit 2 60 false,
    .orbit 3 0 false,
    .orbit 2 0 false,
    .orbit 3 2 false,
    .orbit 2 2 false,
    .orbit 2 86 false,
    .orbit 3 84 true,
    .orbit 3 84 false,
    .orbit 2 84 false] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullTriangleOrbitTable_injective :
    Function.Injective threeHighFullTriangleOrbitTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullTriangleOrbitTable_checked (i : Fin 22) :
    encodedC4Free (threeHighFullTriangleOrbitTableAdj i) = true ∧
    (threeHighFullTriangleOrbitCert i).Valid (threeHighFullTriangleOrbitTableAdj i)
      threeHighFullTriangleTableAdj := by decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighFullTriangleOrbitTable_no_cross (i : Fin 22)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain (threeHighFullTriangleOrbitTableAdj i) R :=
  threeHighFullTriangleOrbit_no_cross _ _ (threeHighFullTriangleOrbitTable_checked i).2 R cross

end Erdos85
#print axioms Erdos85.threeHighFullTriangleOrbitTable_injective
#print axioms Erdos85.threeHighFullTriangleOrbitTable_checked
#print axioms Erdos85.threeHighFullTriangleOrbitTable_no_cross
