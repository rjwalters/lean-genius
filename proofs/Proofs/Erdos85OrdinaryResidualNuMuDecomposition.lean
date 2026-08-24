import Proofs.Erdos85BinaryTransportResidualGraph
import Proofs.Erdos85GraphEdgeIndicatorPotential

/-!
# Ordinary residual price as nu plus mu

On a non-ambient pair, the triangle-free graph contributes nothing to the
residual symmetric difference.  The residual price is therefore the
transport entry `A² + A³`: its quadratic term is the common-neighbor atom
`nu`, and its cubic term is the cross-neighborhood matching parity `mu`.
This is `(73rnz_av)`.
-/

open SimpleGraph

namespace Erdos85

/-- **Ordinary residual atom decomposition (`73rnz_av`), matrix form.** -/
theorem graphEdgeIndicator_binaryTransportResidual_eq_sq_add_cube_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    {u v : V} (hnotA : ¬ A.Adj u v) :
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) u v +
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) u v := by
  let H := binaryTransportSupportGraph A hq hreg
  let T := triangleFreeEdgeGraph A
  have hnotT : ¬ T.Adj u v := by
    intro hT
    exact hnotA ((mem_triangleFreeNeighbors A u v).mp hT).1
  have hKmatrix :
      (binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2) =
        H.adjMatrix (ZMod 2) + T.adjMatrix (ZMod 2) := by
    unfold binaryTransportResidualGraph graphF2SymmetricDifference
    exact f2MatrixSupportGraph_adjMatrix_eq _ _ _
  have hHmatrix : H.adjMatrix (ZMod 2) = binaryTransportMatrix A := by
    exact f2MatrixSupportGraph_adjMatrix_eq _ _ _
  calc
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
        (binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2) u v := by
      simp [graphEdgeIndicator, SimpleGraph.adjMatrix_apply]
    _ = H.adjMatrix (ZMod 2) u v + T.adjMatrix (ZMod 2) u v := by
      rw [hKmatrix, Matrix.add_apply]
    _ = H.adjMatrix (ZMod 2) u v := by
      simp [SimpleGraph.adjMatrix_apply, hnotT]
    _ = binaryTransportMatrix A u v := by rw [hHmatrix]
    _ = ((A.adjMatrix (ZMod 2)) ^ 3 +
          (A.adjMatrix (ZMod 2)) ^ 2) u v := by
      rw [binaryTransportMatrix_eq_cube_add_sq]
    _ = (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) u v +
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) u v := by
      let M := A.adjMatrix (ZMod 2)
      have hpowTwo : M ^ 2 = M * M := by simp [pow_two]
      have hpowThree : M ^ 3 = M * M * M := by
        simp [pow_succ, pow_two, mul_assoc]
      change (M ^ 3 + M ^ 2) u v = (M * M) u v + (M * M * M) u v
      rw [hpowTwo, hpowThree, Matrix.add_apply, add_comm]

/-- The same identity with `nu` displayed literally as the parity of the
common-neighbor fiber. -/
theorem graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    {u v : V} (hnotA : ¬ A.Adj u v) :
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v =
      (((A.neighborFinset u ∩ A.neighborFinset v).card : ℕ) : ZMod 2) +
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) u v := by
  rw [graphEdgeIndicator_binaryTransportResidual_eq_sq_add_cube_of_not_adj
    A hq hreg hnotA]
  rw [adjMatrix_sq_apply_eq_card_common_zmodTwo]

end Erdos85

#print axioms Erdos85.graphEdgeIndicator_binaryTransportResidual_eq_sq_add_cube_of_not_adj
#print axioms Erdos85.graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
