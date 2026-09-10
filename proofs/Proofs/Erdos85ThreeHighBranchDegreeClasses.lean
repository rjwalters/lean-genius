import Proofs.Erdos85ThreeBlockDegreeTotals
import Proofs.Erdos85ThreeHighSecondaryDegreeClasses

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

theorem threeHighFullUnion_secondary_degree_class
    (p : ThreeBlockFullParameters) (q : Fin 21) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeHighFullUnionAdj p)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))) :
    q ∈ threeHighSecondaryDegreeCodes 8 := by
  exact threeHighCrossDomain_secondary_degree_class _ q cross hc 8
    (threeHighFullUnionAdj_degree_total p)

theorem threeHighDeficientUnion_secondary_degree_class
    (p : ThreeBlockDeficientParameters) (q : Fin 21) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain (threeHighDeficientUnionAdj p)
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))) :
    q ∈ threeHighSecondaryDegreeCodes 6 := by
  exact threeHighCrossDomain_secondary_degree_class _ q cross hc 6
    (threeHighDeficientUnionAdj_degree_total p)

end Erdos85
#print axioms Erdos85.threeHighFullUnion_secondary_degree_class
#print axioms Erdos85.threeHighDeficientUnion_secondary_degree_class
