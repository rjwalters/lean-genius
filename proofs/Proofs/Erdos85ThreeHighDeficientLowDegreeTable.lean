import Proofs.Erdos85ThreeHighDeficientLowDegreeExample
import Proofs.Erdos85ThreeBlockCompactCodes

namespace Erdos85

/-- Fifteen explicit deficient configurations rejected by the low-degree bound.
This table is not an exhaustive list of all U configurations. -/
def threeHighDeficientLowDegreeTable (i : Fin 15) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 6 14 4,
    threeBlockDeficientCompactCode 6 9 20 4,
    threeBlockDeficientCompactCode 6 9 55 4,
    threeBlockDeficientCompactCode 6 3 0 4,
    threeBlockDeficientCompactCode 6 10 5 4,
    threeBlockDeficientCompactCode 9 9 5 3,
    threeBlockDeficientCompactCode 9 9 21 3,
    threeBlockDeficientCompactCode 9 9 54 3,
    threeBlockDeficientCompactCode 9 10 4 3,
    threeBlockDeficientCompactCode 9 10 78 3,
    threeBlockDeficientCompactCode 9 4 0 3,
    threeBlockDeficientCompactCode 9 8 14 3,
    threeBlockDeficientCompactCode 9 8 66 3,
    threeBlockDeficientCompactCode 9 13 80 3,
    threeBlockDeficientCompactCode 9 12 82 3] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem threeHighDeficientLowDegreeTable_injective :
    Function.Injective threeHighDeficientLowDegreeTable := by
  decide

def threeHighDeficientLowDegreeTableAdj (i : Fin 15) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientLowDegreeTable i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem threeHighDeficientLowDegreeTable_bad (i : Fin 15) :
    2 ≤ (Finset.univ.filter fun x => encodedRowDegree (threeHighDeficientLowDegreeTableAdj i x) ≤ 1).card := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem threeHighDeficientLowDegreeTable_c4 (i : Fin 15) :
    encodedC4Free (threeHighDeficientLowDegreeTableAdj i) = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDeficientLowDegreeTable_no_cross (i : Fin 15)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain (threeHighDeficientLowDegreeTableAdj i) R := by
  intro hc
  have h := threeHighCrossDomain_low_union_degree_unique _ R cross hc
  have hb := threeHighDeficientLowDegreeTable_bad i
  omega

end Erdos85
#print axioms Erdos85.threeHighDeficientLowDegreeTable_bad
#print axioms Erdos85.threeHighDeficientLowDegreeTable_c4
#print axioms Erdos85.threeHighDeficientLowDegreeTable_no_cross

#print axioms Erdos85.threeHighDeficientLowDegreeTable_injective
