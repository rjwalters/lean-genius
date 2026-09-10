import Proofs.Erdos85ThreeHighSecondaryOrbitTable
import Proofs.Erdos85ThreeHighDegreeBalance

namespace Erdos85

def threeHighSecondaryDegreeCodes (total : Nat) : Finset (Fin 21) :=
  Finset.univ.filter fun q =>
    (∑ j, encodedRowDegree (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q) j)) = total

set_option maxRecDepth 100000 in
theorem threeHighSecondaryDegreeCodes_six :
    threeHighSecondaryDegreeCodes 6 = {0,1,2,4,5,7,9,11} := by decide

set_option maxRecDepth 100000 in
theorem threeHighSecondaryDegreeCodes_eight :
    threeHighSecondaryDegreeCodes 8 = {3,6,8,10,12,13,14,15,16,17,18,19,20} := by decide

theorem threeHighSecondaryDegreeCodes_cards :
    (threeHighSecondaryDegreeCodes 6).card = 8 ∧
    (threeHighSecondaryDegreeCodes 8).card = 13 := by
  rw [threeHighSecondaryDegreeCodes_six,threeHighSecondaryDegreeCodes_eight]
  decide

theorem threeHighSecondaryDegreeCodes_cover :
    threeHighSecondaryDegreeCodes 6 ∪ threeHighSecondaryDegreeCodes 8 = Finset.univ := by
  rw [threeHighSecondaryDegreeCodes_six,threeHighSecondaryDegreeCodes_eight]
  decide

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_secondary_degree_class
    (U : Fin 15 → Fin 15 → Bool) (q : Fin 21) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)))
    (total : Nat) (hU : (∑ i, encodedRowDegree (U i)) = total + 34) :
    q ∈ threeHighSecondaryDegreeCodes total := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have h := threeHighCrossDomain_degree_balance U _ cross hc
  omega

end Erdos85
#print axioms Erdos85.threeHighSecondaryDegreeCodes_six
#print axioms Erdos85.threeHighSecondaryDegreeCodes_eight
#print axioms Erdos85.threeHighSecondaryDegreeCodes_cards
#print axioms Erdos85.threeHighSecondaryDegreeCodes_cover
#print axioms Erdos85.threeHighCrossDomain_secondary_degree_class
