import Proofs.Erdos85ThreeHighFarEdgeLowAdjacent
import Proofs.Erdos85ThreeHighLowDegreePairGate
import Proofs.Erdos85ThreeHighLowDegreeTriangleGate
import Proofs.Erdos85ThreeHighLowDegreePreflight

namespace Erdos85

def threeHighDeficientLowAdjacentTable (i : Fin 8) : ThreeBlockDeficientFirstRowParameters :=
  ![threeBlockDeficientCompactCode 6 9 5 4,
    threeBlockDeficientCompactCode 6 9 16 4,
    threeBlockDeficientCompactCode 6 9 21 4,
    threeBlockDeficientCompactCode 6 9 59 4,
    threeBlockDeficientCompactCode 6 9 61 4,
    threeBlockDeficientCompactCode 6 10 21 4,
    threeBlockDeficientCompactCode 6 10 55 4,
    threeBlockDeficientCompactCode 6 10 59 4] i

def threeHighDeficientLowAdjacentAdj (i : Fin 8) : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed (threeHighDeficientLowAdjacentTable i))

def threeHighDeficientLowAdjacentWitness (i : Fin 8) : Fin 15 × Fin 15 :=
  ![(9,4),(9,4),(9,4),(9,4),(9,4),(9,4),(9,4),(9,4)] i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientLowAdjacentTable_injective :
    Function.Injective threeHighDeficientLowAdjacentTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientLowAdjacentTable_checked (i : Fin 8) :
    let U := threeHighDeficientLowAdjacentAdj i
    let w := threeHighDeficientLowAdjacentWitness i
    encodedRowDegree (U w.1) ≤ 1 ∧ encodedRowDegree (U w.2) ≤ 2 ∧ U w.1 w.2 = true := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighDeficientLowAdjacentTable_prior_filters (i : Fin 8) :
    let U := threeHighDeficientLowAdjacentAdj i
    encodedC4Free U = true ∧ threeHighLowDegreeGate U = true ∧
      threeHighLowDegreeTriangleGate U = true ∧ threeHighLowDegreePairGate U = true := by
  decide +revert

attribute [local irreducible] threeHighCrossDomain

theorem threeHighDeficientLowAdjacentTable_no_cross (i : Fin 8)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain (threeHighDeficientLowAdjacentAdj i) R := by
  intro hc
  obtain ⟨hx,hy,hxy⟩ := threeHighDeficientLowAdjacentTable_checked i
  exact threeHighCrossDomain_far_edge_no_low_adjacent _ R cross hc h67 h76 _ _ hx hy hxy

end Erdos85
#print axioms Erdos85.threeHighDeficientLowAdjacentTable_injective
#print axioms Erdos85.threeHighDeficientLowAdjacentTable_checked
#print axioms Erdos85.threeHighDeficientLowAdjacentTable_prior_filters
#print axioms Erdos85.threeHighDeficientLowAdjacentTable_no_cross
