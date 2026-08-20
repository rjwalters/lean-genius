import Proofs.Erdos85EdgeIndexedServiceEndpointCover

/-! # Eigenvector transfer through edge-indexed service incidence -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Sum a support vector over the two endpoints of each exterior edge. -/
def edgeEndpointSumVector
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (f : V → ℂ) : R.edgeFinset → ℂ :=
  (edgeEndpointIncidenceMatrix R).transpose.mulVec f

/-- On zero-sum vectors, endpoint incidence transports an `H`-eigenvector
with eigenvalue `mu` to a `Cedge`-eigenvector with eigenvalue `-mu`. -/
theorem edgeIndexedService_eigenvector_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (f : V → ℂ) (mu : ℂ)
    (hsum : ∑ x, f x = 0)
    (hf : (H.adjMatrix ℂ).mulVec f = mu • f) :
    (Cedge.adjMatrix ℂ).mulVec (edgeEndpointSumVector R f) =
      (-mu) • edgeEndpointSumVector R f := by
  classical
  let I := edgeEndpointIncidenceMatrix R
  let C := Cedge.adjMatrix ℂ
  let J : Matrix V R.edgeFinset ℂ := fun _ _ ↦ 1
  have hHt : (H.adjMatrix ℂ).transpose = H.adjMatrix ℂ := by
    ext x y
    simp [Matrix.transpose_apply, SimpleGraph.adjMatrix_apply, H.adj_comm]
  have hCt : C.transpose = C := by
    ext a b
    simp [C, Matrix.transpose_apply, SimpleGraph.adjMatrix_apply,
      Cedge.adj_comm]
  have htrans : C * I.transpose + I.transpose * H.adjMatrix ℂ =
      J.transpose := by
    have ht := congrArg Matrix.transpose hservice
    simpa [EdgeIndexedServiceEquation, I, C, J, Matrix.transpose_add,
      Matrix.transpose_mul, hHt, hCt, add_comm] using ht
  have hJzero : J.transpose.mulVec f = 0 := by
    funext a
    simp [J, Matrix.mulVec, dotProduct, hsum]
  have hv := congrArg
    (fun M : Matrix R.edgeFinset V ℂ ↦ M.mulVec f) htrans
  change C.mulVec (I.transpose.mulVec f) =
    (-mu) • I.transpose.mulVec f
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hf, Matrix.mulVec_smul, hJzero] at hv
  ext a
  have ha := congrFun hv a
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    add_eq_zero_iff_eq_neg] at ha
  simpa [neg_smul] using ha

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_eigenvector_transfer
