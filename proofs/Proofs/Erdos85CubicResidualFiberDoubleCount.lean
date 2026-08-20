import Proofs.Erdos85CubicResidualFiberHistogram

/-! # Double counting cubic residual fibers

Every residual edge occurs in the endpoint fiber of each of its two endpoints.
This converts sums of the coordinate-wise histogram bounds into an edge-indexed
row bound.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The service edges whose cubic entry against `a` is residual rather than an
adjacent fixed entry. -/
def cubicResidualEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) : Finset R.edgeFinset :=
  Finset.univ.filter fun b ↦ ¬ Cedge.Adj b a

/-- Endpoint double count: summing a weight over all residual fibers counts
every residual `R`-edge exactly twice. -/
theorem sum_cubicResidualFiber_eq_two_mul_sum_cubicResidualEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (w : R.edgeFinset → ℕ) :
    (∑ u : V, ∑ b ∈ cubicResidualFiber R Cedge u a, w b) =
      2 * ∑ b ∈ cubicResidualEdgeFinset R Cedge a, w b := by
  classical
  simp_rw [cubicResidualFiber, incidentEdgeFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [cubicResidualEdgeFinset, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hba : Cedge.Adj b a
  · simp [hba]
  · have hbcard : b.1.toFinset.card = 2 :=
      R.card_toFinset_mem_edgeFinset b
    have hendpoint :
        (∑ x : V, if x ∈ b.1.toFinset then w b else 0) = 2 * w b := by
      have heq :
          (Finset.univ.filter fun x : V ↦ x ∈ b.1.toFinset) =
            b.1.toFinset := by
        ext x
        simp
      rw [← Finset.sum_filter]
      rw [heq]
      simp [hbcard]
    simpa [hba] using hendpoint

/-- Square-mass specialization of the endpoint double count. -/
theorem sum_residualFiberCubicWalkCount_sq_eq_two_mul_residualEdge_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) :
    (∑ u : V, ∑ b ∈ cubicResidualFiber R Cedge u a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2) =
      2 * ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2 :=
  sum_cubicResidualFiber_eq_two_mul_sum_cubicResidualEdgeFinset
    R Cedge a fun b ↦ (residualFiberCubicWalkCount R Cedge a b) ^ 2

end

end Erdos85

#print axioms Erdos85.sum_cubicResidualFiber_eq_two_mul_sum_cubicResidualEdgeFinset
#print axioms Erdos85.sum_residualFiberCubicWalkCount_sq_eq_two_mul_residualEdge_sq
