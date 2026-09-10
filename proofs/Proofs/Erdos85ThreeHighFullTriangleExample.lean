import Proofs.Erdos85ThreeHighLowDegreeTriangle
import Proofs.Erdos85ThreeBlockFirstRowDomain
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates

namespace Erdos85

/-- The full-U fixture used in the earlier bounded runtime diagnostics. -/
def threeHighFullTriangleExample : ThreeBlockFirstRowParameters :=
  (fun _ => ⟨34, by decide⟩, Equiv.swap 1 2)

def threeHighFullTriangleExampleAdj : Fin 15 → Fin 15 → Bool :=
  threeHighFullUnionAdj (threeBlockFirstRowEmbed threeHighFullTriangleExample)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem threeHighFullTriangleExample_c4free :
    encodedC4Free threeHighFullTriangleExampleAdj = true := by decide

attribute [local irreducible] threeHighCrossDomain

/-- Despite its C4-free U graph, this fixture has no degree-valid C4-free E24 completion. -/
theorem threeHighFullTriangleExample_no_cross
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain threeHighFullTriangleExampleAdj R := by
  intro hc
  apply threeHighCrossDomain_no_low_degree_triangle threeHighFullTriangleExampleAdj R cross hc
    4 9 14 (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact ⟨14,by decide,by decide⟩
  · exact ⟨9,by decide,by decide⟩
  · exact ⟨4,by decide,by decide⟩

end Erdos85
#print axioms Erdos85.threeHighFullTriangleExample_c4free
#print axioms Erdos85.threeHighFullTriangleExample_no_cross
