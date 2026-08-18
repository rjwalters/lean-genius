import Proofs.Erdos85CommutingShiftedEigenvector
import Proofs.Erdos85NegativeDegreeEigenvectorRigidity

/-! # A commuting graph operator preserves a signed negative eigenline

This is the graph-facing bridge used for a connected even owner cycle: its
alternating signed vector spans the integral negative-degree eigenspace, so
every commuting defect block acts on that vector by an integral scalar.
-/

open SimpleGraph Matrix

namespace Erdos85

/-- A commuting graph adjacency operator acts by an integral scalar on a
signed negative-degree eigenvector of a connected regular graph. -/
theorem commutingGraph_exists_eigenvalue_on_signed_negativeDegree_line
    {V : Type*} [Fintype V] [DecidableEq V]
    (H D : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel D.Adj]
    (hconn : H.Connected) (k : ℕ) (hreg : ∀ x, H.degree x = k)
    (v : V → ℤ) (hvSign : ∀ x, v x = -1 ∨ v x = 1)
    (hvEigen : ∀ x, ∑ y ∈ H.neighborFinset x, v y = -(k : ℤ) * v x)
    (hcomm : D.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * D.adjMatrix ℤ) :
    ∃ mu : ℤ, (D.adjMatrix ℤ).mulVec v = mu • v := by
  have hHv : (H.adjMatrix ℤ).mulVec v = (-(k : ℤ)) • v := by
    funext x
    rw [SimpleGraph.adjMatrix_mulVec_apply, hvEigen x]
    simp [Pi.smul_apply]
  apply commuting_mulVec_eq_smul_of_eigenline
    (D.adjMatrix ℤ) (H.adjMatrix ℤ) hcomm v (-(k : ℤ)) hHv
  intro w hw
  apply negativeDegree_eigenvector_eq_smul_of_signed H hconn k hreg v hvSign hvEigen w
  intro x
  have hx := congrFun hw x
  rw [SimpleGraph.adjMatrix_mulVec_apply] at hx
  simpa [Pi.smul_apply, smul_eq_mul] using hx

end Erdos85

#print axioms Erdos85.commutingGraph_exists_eigenvalue_on_signed_negativeDegree_line
