import Proofs.Erdos85ThreeHighDeficientLowDegreeTable
import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85

/-- At most one U vertex may require three or more cross neighbors. -/
def threeHighLowDegreeGate (U : Fin 15 → Fin 15 → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => encodedRowDegree (U i) ≤ 1).card ≤ 1)

attribute [local irreducible] threeHighCrossDomain

theorem threeHighLowDegreeGate_of_cross
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) :
    threeHighLowDegreeGate U = true := by
  exact decide_eq_true (threeHighCrossDomain_low_union_degree_unique U R cross hc)

/-- Test the fixed U obstruction before evaluating the supplied search. -/
def threeHighLowDegreePreflight (search : ThreeHighExternalSearch) : ThreeHighExternalSearch :=
  fun U R accept => threeHighLowDegreeGate U && search U R accept

theorem threeHighLowDegreePreflight_sound (search : ThreeHighExternalSearch)
    (hs : ThreeHighExternalSearchSound search) :
    ThreeHighExternalSearchSound (threeHighLowDegreePreflight search) := by
  intro U R accept cross hc hExt ha
  simp only [threeHighLowDegreePreflight, Bool.and_eq_true]
  exact ⟨threeHighLowDegreeGate_of_cross U R cross hc, hs U R accept cross hc hExt ha⟩

theorem threeHighLowDegreeGate_table_false (i : Fin 15) :
    threeHighLowDegreeGate (threeHighDeficientLowDegreeTableAdj i) = false := by
  have h := threeHighDeficientLowDegreeTable_bad i
  simp only [threeHighLowDegreeGate,decide_eq_false_iff_not]
  omega

/-- All fifteen entries reject without making any assumption about downstream search. -/
theorem threeHighLowDegreePreflight_table_false (search : ThreeHighExternalSearch)
    (i : Fin 15) (R : Fin 8 → Fin 8 → Bool) (accept : ThreeHighCross → Bool) :
    threeHighLowDegreePreflight search (threeHighDeficientLowDegreeTableAdj i) R accept = false := by
  simp only [threeHighLowDegreePreflight,threeHighLowDegreeGate_table_false,Bool.false_and]

end Erdos85
#print axioms Erdos85.threeHighLowDegreeGate_of_cross
#print axioms Erdos85.threeHighLowDegreePreflight_sound
#print axioms Erdos85.threeHighLowDegreeGate_table_false
#print axioms Erdos85.threeHighLowDegreePreflight_table_false
