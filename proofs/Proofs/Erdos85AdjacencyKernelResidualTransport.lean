import Proofs.Erdos85OrdinaryResidualNuMuDecomposition

/-!
# Adjacency-kernel weighted residual transport

The scalar centerwise balance loses the empty-star label.  The separator
branch of `(73rnz_ay)` instead weights incidences by a vector in the ambient
adjacency kernel.  Since the transport matrix is `H=A²(A+I)`, it kills every
such weight, and therefore the residual graph `K=H△T` acts exactly as the
triangle-free-edge graph `T` on that weight.
-/

open SimpleGraph

namespace Erdos85

/-- The polynomial transport matrix `A²(A+I)` kills every vector killed by
ambient adjacency. -/
theorem binaryTransportMatrix_mulVec_eq_zero_of_adjMatrix_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (v : V → ZMod 2)
    (hAv : (A.adjMatrix (ZMod 2)).mulVec v = 0) :
    (binaryTransportMatrix A).mulVec v = 0 := by
  let M := A.adjMatrix (ZMod 2)
  change (M * M * (M + 1)).mulVec v = 0
  have hplus : (M + 1).mulVec v = v := by
    rw [Matrix.add_mulVec, hAv, Matrix.one_mulVec, zero_add]
  rw [← Matrix.mulVec_mulVec, hplus, ← Matrix.mulVec_mulVec, hAv,
    Matrix.mulVec_zero]

/-- **Kernel-separator transport (`73rnz_ay`).**  On an ambient adjacency
kernel vector, the residual graph and triangle-free-edge graph have the same
weighted incidence vector. -/
theorem binaryTransportResidualGraph_mulVec_eq_triangleFreeEdgeGraph_mulVec_of_kernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (v : V → ZMod 2)
    (hAv : (A.adjMatrix (ZMod 2)).mulVec v = 0) :
    ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec v =
      ((triangleFreeEdgeGraph A).adjMatrix (ZMod 2)).mulVec v := by
  let H := binaryTransportSupportGraph A hq hreg
  let T := triangleFreeEdgeGraph A
  have hKmatrix :
      (binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2) =
        H.adjMatrix (ZMod 2) + T.adjMatrix (ZMod 2) := by
    unfold binaryTransportResidualGraph graphF2SymmetricDifference
    exact f2MatrixSupportGraph_adjMatrix_eq _ _ _
  have hHmatrix : H.adjMatrix (ZMod 2) = binaryTransportMatrix A :=
    f2MatrixSupportGraph_adjMatrix_eq _ _ _
  rw [hKmatrix, Matrix.add_mulVec, hHmatrix,
    binaryTransportMatrix_mulVec_eq_zero_of_adjMatrix_mulVec_eq_zero A v hAv,
    zero_add]

/-- Coordinate form of the kernel-separator transport, retaining the weight
on every endpoint rather than summing away the star label. -/
theorem sum_graphEdgeIndicator_mul_kernelWeight_residual_eq_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (v : V → ZMod 2)
    (hAv : (A.adjMatrix (ZMod 2)).mulVec v = 0)
    (center : V) :
    (∑ z, graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
      center z * v z) =
      ∑ z, graphEdgeIndicator (triangleFreeEdgeGraph A) center z * v z := by
  have h := congrFun
    (binaryTransportResidualGraph_mulVec_eq_triangleFreeEdgeGraph_mulVec_of_kernel
      A hq hreg v hAv) center
  simpa [Matrix.mulVec, dotProduct, graphEdgeIndicator,
    SimpleGraph.adjMatrix_apply] using h

/-- A genuine two-star separator (`v E₁ + v E₂ = 1`) survives in the
weighted residual/triangle transport equation before any scalar aggregate is
taken. -/
theorem exists_star_distinguishing_weighted_transport_of_kernel_separator
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (E₁ E₂ : V)
    (hsep : ∃ v : V → ZMod 2,
      (A.adjMatrix (ZMod 2)).mulVec v = 0 ∧ v E₁ + v E₂ = 1) :
    ∃ v : V → ZMod 2,
      v E₁ + v E₂ = 1 ∧
      ∀ center,
        (∑ z, graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
          center z * v z) =
        ∑ z, graphEdgeIndicator (triangleFreeEdgeGraph A) center z * v z := by
  rcases hsep with ⟨v, hAv, hv⟩
  exact ⟨v, hv, fun center =>
    sum_graphEdgeIndicator_mul_kernelWeight_residual_eq_triangleFree
      A hq hreg v hAv center⟩

end Erdos85

#print axioms Erdos85.binaryTransportMatrix_mulVec_eq_zero_of_adjMatrix_mulVec_eq_zero
#print axioms Erdos85.binaryTransportResidualGraph_mulVec_eq_triangleFreeEdgeGraph_mulVec_of_kernel
#print axioms Erdos85.sum_graphEdgeIndicator_mul_kernelWeight_residual_eq_triangleFree
#print axioms Erdos85.exists_star_distinguishing_weighted_transport_of_kernel_separator
