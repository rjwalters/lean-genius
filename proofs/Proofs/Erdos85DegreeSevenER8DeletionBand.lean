import Proofs.Erdos85ER8DeletionBand

/-! # Degree-seven deletions of ER(8) -/

namespace Erdos85

def er8DegreeSevenDelete1 : Finset (Fin 73) := {43}
def er8DegreeSevenDelete2 : Finset (Fin 73) := {32,47}
def er8DegreeSevenDelete3 : Finset (Fin 73) := {8,12,14}
def er8DegreeSevenDelete4 : Finset (Fin 73) := {26,39,53,68}
def er8DegreeSevenDelete5 : Finset (Fin 73) := {1,25,54,67,72}
def er8DegreeSevenDelete6 : Finset (Fin 73) := {26,37,38,47,53,54}
def er8DegreeSevenDelete7 : Finset (Fin 73) := {20,29,32,52,59,62,72}
def er8DegreeSevenDelete8 : Finset (Fin 73) := {3,6,42,48,51,62,64,66}
def er8DegreeSevenDelete9 : Finset (Fin 73) := {2,4,9,21,31,37,38,43,55}
def er8DegreeSevenDelete10 : Finset (Fin 73) := {3,16,28,29,37,41,42,46,52,62}

private theorem er8_degreeSeven_delete_witness
    (S : Finset (Fin 73)) (n : ℕ)
    (hcard : Fintype.card {v : Fin 73 // v ∉ S} = n)
    (hmin : 7 ≤ (er8DeleteGraph S).minDegree) :
    C4FreeMinDegreeWitness n 7 := by
  apply c4FreeMinDegreeWitness_of_card_eq (er8DeleteGraph S)
  · exact hcard
  · exact hmin
  · exact er8DeleteGraph_not_containsC4 S

theorem er8_delete1_degreeSeven_witness : C4FreeMinDegreeWitness 72 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete1 72 (by native_decide) (by native_decide)
theorem er8_delete2_degreeSeven_witness : C4FreeMinDegreeWitness 71 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete2 71 (by native_decide) (by native_decide)
theorem er8_delete3_degreeSeven_witness : C4FreeMinDegreeWitness 70 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete3 70 (by native_decide) (by native_decide)
theorem er8_delete4_degreeSeven_witness : C4FreeMinDegreeWitness 69 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete4 69 (by native_decide) (by native_decide)
theorem er8_delete5_degreeSeven_witness : C4FreeMinDegreeWitness 68 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete5 68 (by native_decide) (by native_decide)
theorem er8_delete6_degreeSeven_witness : C4FreeMinDegreeWitness 67 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete6 67 (by native_decide) (by native_decide)
theorem er8_delete7_degreeSeven_witness : C4FreeMinDegreeWitness 66 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete7 66 (by native_decide) (by native_decide)
theorem er8_delete8_degreeSeven_witness : C4FreeMinDegreeWitness 65 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete8 65 (by native_decide) (by native_decide)
theorem er8_delete9_degreeSeven_witness : C4FreeMinDegreeWitness 64 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete9 64 (by native_decide) (by native_decide)
theorem er8_delete10_degreeSeven_witness : C4FreeMinDegreeWitness 63 7 :=
  er8_degreeSeven_delete_witness er8DegreeSevenDelete10 63 (by native_decide) (by native_decide)

theorem er8_degreeSeven_witness : C4FreeMinDegreeWitness 73 7 := by
  refine ⟨er8Graph, inferInstance, ?_, er8Graph_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  exact (er8Graph_degree_ge_eight v).trans' (by norm_num)

/-- A continuous degree-seven witness band at orders 63--73. -/
theorem degreeSeven_witness_sixtyThree_add (j : ℕ) (hj : j ≤ 10) :
    C4FreeMinDegreeWitness (63 + j) 7 := by
  interval_cases j <;> norm_num
  · exact er8_delete10_degreeSeven_witness
  · exact er8_delete9_degreeSeven_witness
  · exact er8_delete8_degreeSeven_witness
  · exact er8_delete7_degreeSeven_witness
  · exact er8_delete6_degreeSeven_witness
  · exact er8_delete5_degreeSeven_witness
  · exact er8_delete4_degreeSeven_witness
  · exact er8_delete3_degreeSeven_witness
  · exact er8_delete2_degreeSeven_witness
  · exact er8_delete1_degreeSeven_witness
  · exact er8_degreeSeven_witness

end Erdos85
