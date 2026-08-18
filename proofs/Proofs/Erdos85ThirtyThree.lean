import Proofs.Erdos85DegreeSixEmptySector

/-!
# The exact order-33 value for Erdős Problem 85

The explicit graph below is an induced 33-vertex subgraph of the verified
order-49 degree-six witness.  Its minimum degree is five, and its common-
neighbour matrix certifies that it is `C₄`-free.  Together with the degree-six
boundary exclusion, this pins the threshold at order 33 exactly.
-/

namespace Erdos85

open SimpleGraph

def degreeFiveThirtyThreeEdges : List (Fin 33 × Fin 33) :=
  [(0,28), (0,29), (0,30), (0,31), (0,32),
   (1,5), (1,14), (1,21), (1,27), (1,28),
   (2,12), (2,16), (2,18), (2,19), (2,24), (2,28),
   (3,4), (3,10), (3,13), (3,20), (3,28),
   (4,9), (4,17), (4,26), (4,28),
   (5,7), (5,11), (5,15), (5,23), (5,28),
   (6,22), (6,23), (6,24), (6,25), (6,26), (6,27),
   (7,10), (7,18), (7,22), (7,32),
   (8,9), (8,14), (8,15), (8,20), (8,22), (8,30),
   (9,11), (9,19), (9,22), (9,31),
   (10,13), (10,16), (10,22),
   (11,12), (11,23), (11,31),
   (12,20), (12,26), (12,32),
   (13,14), (13,19), (13,25), (13,29),
   (14,18), (14,27), (14,30),
   (15,17), (15,20), (15,24),
   (16,21), (16,23), (16,30),
   (17,18), (17,26), (17,29),
   (18,31), (19,24), (19,29),
   (20,21), (20,32),
   (21,25), (21,31),
   (23,29), (24,27),
   (25,26), (25,31),
   (26,30), (27,32), (29,32)]

/-- An explicit `C₄`-free graph on 33 vertices of minimum degree five. -/
def degreeFiveThirtyThree : SimpleGraph (Fin 33) where
  Adj i j :=
    (i, j) ∈ degreeFiveThirtyThreeEdges ∨
      (j, i) ∈ degreeFiveThirtyThreeEdges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by native_decide

instance : DecidableRel degreeFiveThirtyThree.Adj := fun i j =>
  decidable_of_iff
    ((i, j) ∈ degreeFiveThirtyThreeEdges ∨
      (j, i) ∈ degreeFiveThirtyThreeEdges) Iff.rfl

theorem degreeFiveThirtyThree_five_le_degree :
    ∀ v : Fin 33, 5 ≤ degreeFiveThirtyThree.degree v := by
  native_decide

theorem degreeFiveThirtyThree_common_le_one :
    ∀ x y : Fin 33, x ≠ y →
      (degreeFiveThirtyThree.neighborFinset x ∩
        degreeFiveThirtyThree.neighborFinset y).card ≤ 1 := by
  native_decide

theorem degreeFiveThirtyThree_not_containsC4 :
    ¬ containsC4 (Fin 33) degreeFiveThirtyThree :=
  not_containsC4_of_forall_common_le_one degreeFiveThirtyThree_common_le_one

theorem degreeFiveThirtyThree_five_le_minDegree :
    5 ≤ degreeFiveThirtyThree.minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact degreeFiveThirtyThree_five_le_degree

theorem five_lt_minDegreeForC4_thirtyThree :
    5 < minDegreeForC4 33 := by
  apply (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).1
  exact ⟨degreeFiveThirtyThree, inferInstance,
    degreeFiveThirtyThree_five_le_minDegree,
    degreeFiveThirtyThree_not_containsC4⟩

/-- **`f(33) = 6`.** -/
theorem minDegreeForC4_thirtyThree : minDegreeForC4 33 = 6 := by
  have hupper := minDegreeForC4_thirtyThree_le_six
  have hlower := five_lt_minDegreeForC4_thirtyThree
  omega

end Erdos85
