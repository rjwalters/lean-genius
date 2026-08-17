import Proofs.Erdos85CrossDefectComponentCommonNeighbor

/-!
# Incidence orthogonality across defect components

The owner Gram matrices arise from rectangular ambient-neighbor incidence
matrices.  Distinct defect components have constant all-ones cross Gram.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ambient-neighbor incidence with columns restricted to a defect component. -/
def defectComponentNeighborIncidenceMatrix
    {K V : Type*} [Fintype V] [DecidableEq V] [Zero K] [One K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix V c.supp K :=
  fun x z => if G.Adj x z.1 then 1 else 0

/-- Distinct defect-component incidence systems are orthogonal designs:
every pair of columns has exactly one common row. -/
theorem transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
        defectComponentNeighborIncidenceMatrix (K := ℤ) G d =
      Matrix.of fun _ _ => (1 : ℤ) := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, defectComponentNeighborIncidenceMatrix,
    Matrix.of_apply, ite_mul, one_mul, zero_mul]
  calc
    (∑ z : V, if G.Adj z x.1 then if G.Adj z y.1 then (1 : ℤ) else 0 else 0) =
        ∑ z : V, if G.Adj x.1 z ∧ G.Adj y.1 z then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hzx : G.Adj z x.1 <;> by_cases hzy : G.Adj z y.1 <;>
        simp [hzx, hzy, G.adj_comm]
    _ = ((G.neighborFinset x.1 ∩ G.neighborFinset y.1).card : ℤ) := by
      rw [Finset.sum_boole]
      have hfilt : (Finset.univ : Finset V).filter
          (fun z => G.Adj x.1 z ∧ G.Adj y.1 z) =
          G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
        ext z
        simp [SimpleGraph.mem_neighborFinset]
      rw [hfilt]
    _ = 1 := by
      rw [card_common_eq_one_of_mem_distinct_secondOrderDefect_components
        G hfree hcd x y]
      norm_num

end

end Erdos85
