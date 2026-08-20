import Proofs.Erdos85EdgeIndexedServiceIncidenceKernel

/-!
# The quotient operator of an edge-indexed service graph

Modulo the endpoint-incidence kernel, service adjacency is the centered
negative adjacency operator on the endpoint graph.  This is the algebraic
bridge from the explicit endpoint spectrum to the 16-dimensional quotient
and, subsequently, to the 32-dimensional residual moment ledger.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The square all-ones matrix on the endpoint vertex type. -/
def edgeIndexedVertexOnesMatrix (V : Type*) : Matrix V V ℂ := fun _ _ ↦ 1

/-- Every endpoint-incidence column has coordinate sum two. -/
theorem sum_edgeEndpointIncidenceMatrix_column
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (a : R.edgeFinset) :
    ∑ u, edgeEndpointIncidenceMatrix R u a = (2 : ℂ) := by
  classical
  unfold edgeEndpointIncidenceMatrix
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [show (Finset.univ.filter fun u : V ↦ u ∈ a.1.toFinset) =
      a.1.toFinset by ext u; simp]
  exact_mod_cast R.card_toFinset_mem_edgeFinset a

/-- Half the all-ones vertex matrix composed with endpoint incidence is the
rectangular all-ones service matrix. -/
theorem half_ones_mul_edgeEndpointIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] :
    ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V) *
        edgeEndpointIncidenceMatrix R =
      edgeIndexedOnesMatrix R := by
  classical
  ext u a
  rw [Matrix.mul_apply]
  simp only [Matrix.smul_apply, edgeIndexedVertexOnesMatrix,
    edgeIndexedOnesMatrix]
  rw [← Finset.mul_sum, sum_edgeEndpointIncidenceMatrix_column R a]
  norm_num

/-- The service equation descends along endpoint incidence: on the quotient
by `ker I`, service adjacency is represented by `(1/2)J - A_H`. -/
theorem edgeIndexedService_quotient_intertwining
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge) :
    edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ =
      ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ) *
        edgeEndpointIncidenceMatrix R := by
  unfold EdgeIndexedServiceEquation at hservice
  change H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R +
    edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ =
      edgeIndexedOnesMatrix R at hservice
  calc
    edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ =
        edgeIndexedOnesMatrix R -
          H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R := by
      rw [← hservice]
      abel
    _ = ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V) *
          edgeEndpointIncidenceMatrix R -
        H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R := by
      rw [half_ones_mul_edgeEndpointIncidenceMatrix R]
    _ = ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ) *
          edgeEndpointIncidenceMatrix R := by
      rw [Matrix.sub_mul]

/-- Vector form of the quotient intertwining identity. -/
theorem edgeIndexedService_quotient_intertwining_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (x : R.edgeFinset → ℂ) :
    (edgeEndpointIncidenceMatrix R).mulVec
        ((Cedge.adjMatrix ℂ).mulVec x) =
      ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ).mulVec
        ((edgeEndpointIncidenceMatrix R).mulVec x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    edgeIndexedService_quotient_intertwining H R Cedge hservice]

/-- The quotient intertwining propagates to every power, providing the direct
bridge for all spectral moments. -/
theorem edgeIndexedService_quotient_intertwining_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (n : ℕ) :
    edgeEndpointIncidenceMatrix R * (Cedge.adjMatrix ℂ) ^ n =
      ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ) ^ n *
        edgeEndpointIncidenceMatrix R := by
  let I := edgeEndpointIncidenceMatrix R
  let C := Cedge.adjMatrix ℂ
  let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
  have hIC : I * C = B * I :=
    edgeIndexedService_quotient_intertwining H R Cedge hservice
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc, hIC, ← Matrix.mul_assoc]

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_quotient_intertwining
#print axioms Erdos85.edgeIndexedService_quotient_intertwining_mulVec
#print axioms Erdos85.edgeIndexedService_quotient_intertwining_pow
