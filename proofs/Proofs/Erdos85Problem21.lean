import Proofs.Erdos85Problem

/-!
# The exact value at 21

The explicit extremal graph at order 20 admits a safe four-vertex attachment.
This extends the checked plateau by one point and illustrates that the generic
attachment criterion can succeed even though it fails uniformly over all
degree-four witnesses.
-/

namespace Erdos85

/-- Four vertices of `twentyRegular` with pairwise disjoint neighborhoods. -/
def twentySafeFour : Finset (Fin 20) := {8, 12, 13, 18}

theorem twentySafeFour_card : twentySafeFour.card = 4 := by decide

theorem twentySafeFour_commonNeighborIndependent :
    CommonNeighborIndependent twentyRegular twentySafeFour := by
  unfold CommonNeighborIndependent
  decide

/-- A `C₄`-free graph on 21 vertices with minimum degree at least four. -/
theorem twentyone_degree_four_witness : C4FreeMinDegreeWitness 21 4 := by
  have hmin : 4 ≤ twentyRegular.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [twentyRegular_degree v]
  have hfree : ¬ containsC4 (Fin 20) twentyRegular :=
    not_containsC4_of_forall_common_le_one twentyRegular_common_le_one
  simpa using c4FreeMinDegreeWitness_succ_of_commonNeighborIndependent
    twentyRegular hmin hfree
    twentySafeFour (by rw [twentySafeFour_card])
    twentySafeFour_commonNeighborIndependent

/-- **`f(21) = 5`.** -/
theorem minDegreeForC4_twentyone : minDegreeForC4 21 = 5 := by
  have hlt : 4 < minDegreeForC4 21 :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).1
      twentyone_degree_four_witness
  have hle := minDegreeForC4_twentyone_le
  omega

end Erdos85
