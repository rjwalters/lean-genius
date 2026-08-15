import Proofs.Erdos85Problem21
import Proofs.Erdos85DegreeFiveBoundaryPackage

/-!
# The finite degree-four witness band

The checked order-21 witness begins the band.  Four further induced subgraphs
of `ER(5)` fill orders 22--25; from order 26 onward the completed degree-five
construction can simply be weakened.
-/

namespace Erdos85

def er5DegreeFourDelete6 : Finset (Fin 31) := {1,9,19,22,23,28}
def er5DegreeFourDelete7 : Finset (Fin 31) := {1,8,9,19,20,22,28}
def er5DegreeFourDelete8 : Finset (Fin 31) := {1,4,8,9,10,14,17,27}
def er5DegreeFourDelete9 : Finset (Fin 31) := {0,1,2,4,25,26,27,28,30}

theorem er5_delete6_degreeFour_witness : C4FreeMinDegreeWitness 25 4 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5DegreeFourDelete6)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5DegreeFourDelete6

theorem er5_delete7_degreeFour_witness : C4FreeMinDegreeWitness 24 4 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5DegreeFourDelete7)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5DegreeFourDelete7

theorem er5_delete8_degreeFour_witness : C4FreeMinDegreeWitness 23 4 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5DegreeFourDelete8)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5DegreeFourDelete8

theorem er5_delete9_degreeFour_witness : C4FreeMinDegreeWitness 22 4 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er5DeleteGraph er5DegreeFourDelete9)
  · native_decide
  · native_decide
  · exact er5DeleteGraph_not_containsC4 er5DegreeFourDelete9

/-- Every order at least 21 carries a degree-four witness. -/
theorem degreeFour_witness_of_twentyOne_le
    {n : ℕ} (hn : 21 ≤ n) :
    C4FreeMinDegreeWitness n 4 := by
  by_cases h26 : n < 26
  · interval_cases n
    · exact twentyone_degree_four_witness
    · exact er5_delete9_degreeFour_witness
    · exact er5_delete8_degreeFour_witness
    · exact er5_delete7_degreeFour_witness
    · exact er5_delete6_degreeFour_witness
  · exact (degreeFive_witness_of_twentySix_le (by omega)).mono_degree (by norm_num)

end Erdos85
