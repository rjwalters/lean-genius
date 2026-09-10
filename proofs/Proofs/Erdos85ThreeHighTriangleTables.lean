import Proofs.Erdos85ThreeHighTrianglePreflight
import Proofs.Erdos85ThreeBlockCompactCodes

namespace Erdos85

attribute [local irreducible] threeHighCrossDomain

/-- Explicit full configurations rejected by the triangle obstruction.
This finite table does not assert exhaustive orbit coverage. -/
def threeHighFullTriangleTable (i : Fin 4) : ThreeBlockFirstRowParameters :=
  ![threeBlockCompactCode 6 6 14,
    threeBlockCompactCode 6 3 0,
    threeBlockCompactCode 9 9 55,
    threeBlockCompactCode 9 4 1] i

def threeHighFullTriangleTableAdj (i : Fin 4) : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed (threeHighFullTriangleTable i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullTriangleTable_injective :
    Function.Injective threeHighFullTriangleTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullTriangleTable_checked :
    ∀ i : Fin 4, encodedC4Free (threeHighFullTriangleTableAdj i) = true ∧
      threeHighLowDegreeTriangleGate (threeHighFullTriangleTableAdj i) = false := by decide

theorem threeHighFullTriangleTable_no_cross (i : Fin 4)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain (threeHighFullTriangleTableAdj i) R := by
  intro hc
  have ht := threeHighLowDegreeTriangleGate_of_cross (threeHighFullTriangleTableAdj i) R cross hc
  rw [(threeHighFullTriangleTable_checked i).2] at ht
  cases ht

theorem threeHighFullTriangleTable_search_false (search : ThreeHighExternalSearch) (i : Fin 4)
    (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) :
    threeHighTrianglePreflight search (threeHighFullTriangleTableAdj i) R accept = false := by
  simp only [threeHighTrianglePreflight,(threeHighFullTriangleTable_checked i).2,Bool.false_and]

/-- Explicit deficient configurations rejected by the triangle obstruction.
This finite table does not assert exhaustive orbit coverage. -/
def threeHighDeficientTriangleTable (i : Fin 35) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 6 14 0,
    threeBlockDeficientCompactCode 6 6 14 1,
    threeBlockDeficientCompactCode 6 9 14 0,
    threeBlockDeficientCompactCode 6 9 54 2,
    threeBlockDeficientCompactCode 6 3 0 0,
    threeBlockDeficientCompactCode 6 10 0 0,
    threeBlockDeficientCompactCode 6 10 54 2,
    threeBlockDeficientCompactCode 9 9 1 1,
    threeBlockDeficientCompactCode 9 9 1 2,
    threeBlockDeficientCompactCode 9 9 5 0,
    threeBlockDeficientCompactCode 9 9 14 0,
    threeBlockDeficientCompactCode 9 9 15 0,
    threeBlockDeficientCompactCode 9 9 16 0,
    threeBlockDeficientCompactCode 9 9 21 0,
    threeBlockDeficientCompactCode 9 9 44 0,
    threeBlockDeficientCompactCode 9 9 55 0,
    threeBlockDeficientCompactCode 9 9 55 1,
    threeBlockDeficientCompactCode 9 9 58 0,
    threeBlockDeficientCompactCode 9 10 0 0,
    threeBlockDeficientCompactCode 9 10 1 0,
    threeBlockDeficientCompactCode 9 10 21 0,
    threeBlockDeficientCompactCode 9 10 55 2,
    threeBlockDeficientCompactCode 9 10 79 0,
    threeBlockDeficientCompactCode 9 10 81 4,
    threeBlockDeficientCompactCode 9 4 1 0,
    threeBlockDeficientCompactCode 9 4 1 2,
    threeBlockDeficientCompactCode 9 4 15 4,
    threeBlockDeficientCompactCode 9 7 13 2,
    threeBlockDeficientCompactCode 9 7 15 4,
    threeBlockDeficientCompactCode 9 7 16 0,
    threeBlockDeficientCompactCode 9 8 15 0,
    threeBlockDeficientCompactCode 9 8 55 0,
    threeBlockDeficientCompactCode 9 13 1 2,
    threeBlockDeficientCompactCode 9 13 55 0,
    threeBlockDeficientCompactCode 9 13 79 4] i

def threeHighDeficientTriangleTableAdj (i : Fin 35) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientTriangleTable i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientTriangleTable_injective :
    Function.Injective threeHighDeficientTriangleTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientTriangleTable_checked :
    ∀ i : Fin 35, encodedC4Free (threeHighDeficientTriangleTableAdj i) = true ∧
      threeHighLowDegreeTriangleGate (threeHighDeficientTriangleTableAdj i) = false := by decide

theorem threeHighDeficientTriangleTable_no_cross (i : Fin 35)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain (threeHighDeficientTriangleTableAdj i) R := by
  intro hc
  have ht := threeHighLowDegreeTriangleGate_of_cross (threeHighDeficientTriangleTableAdj i) R cross hc
  rw [(threeHighDeficientTriangleTable_checked i).2] at ht
  cases ht

theorem threeHighDeficientTriangleTable_search_false (search : ThreeHighExternalSearch) (i : Fin 35)
    (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) :
    threeHighTrianglePreflight search (threeHighDeficientTriangleTableAdj i) R accept = false := by
  simp only [threeHighTrianglePreflight,(threeHighDeficientTriangleTable_checked i).2,Bool.false_and]

end Erdos85
#print axioms Erdos85.threeHighFullTriangleTable_injective
#print axioms Erdos85.threeHighFullTriangleTable_checked
#print axioms Erdos85.threeHighFullTriangleTable_no_cross
#print axioms Erdos85.threeHighFullTriangleTable_search_false
#print axioms Erdos85.threeHighDeficientTriangleTable_injective
#print axioms Erdos85.threeHighDeficientTriangleTable_checked
#print axioms Erdos85.threeHighDeficientTriangleTable_no_cross
#print axioms Erdos85.threeHighDeficientTriangleTable_search_false
