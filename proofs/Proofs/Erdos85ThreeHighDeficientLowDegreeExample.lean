import Proofs.Erdos85ThreeHighLargeCrossRows
import Proofs.Erdos85ThreeBlockFirstRowDomain
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates

namespace Erdos85

/-- Retained deficient representative 6: masks 129/20/20, swap 1/3, omit 4. -/
def threeHighDeficientLowDegreeExample : ThreeBlockDeficientFirstRowParameters :=
  ((fun _ => ⟨20,by decide⟩,Equiv.swap 1 3),4)

def threeHighDeficientLowDegreeExampleAdj : Fin 15 → Fin 15 → Bool :=
  threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed threeHighDeficientLowDegreeExample)

set_option maxRecDepth 100000 in
theorem threeHighDeficientLowDegreeExample_bad :
    2 ≤ (Finset.univ.filter fun i => encodedRowDegree (threeHighDeficientLowDegreeExampleAdj i) ≤ 1).card := by
  decide

set_option maxRecDepth 100000 in
theorem threeHighDeficientLowDegreeExample_c4 :
    encodedC4Free threeHighDeficientLowDegreeExampleAdj = true := by
  decide

attribute [local irreducible] threeHighCrossDomain

/-- No secondary graph or cross matrix can complete this U configuration. -/
theorem threeHighDeficientLowDegreeExample_no_cross
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross) :
    cross ∉ threeHighCrossDomain threeHighDeficientLowDegreeExampleAdj R := by
  intro hc
  have h := threeHighCrossDomain_low_union_degree_unique _ R cross hc
  have hb := threeHighDeficientLowDegreeExample_bad
  omega

end Erdos85
#print axioms Erdos85.threeHighDeficientLowDegreeExample_bad
#print axioms Erdos85.threeHighDeficientLowDegreeExample_no_cross

#print axioms Erdos85.threeHighDeficientLowDegreeExample_c4
