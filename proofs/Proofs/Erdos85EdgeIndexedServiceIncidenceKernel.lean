import Proofs.Erdos85EdgeIndexedServiceSquaredEquation
import Proofs.Erdos85EdgeIndexedServiceEigenvectorTransfer

/-! # The residual incidence kernel of an edge-indexed service graph -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Summing endpoint-incidence coordinates counts every exterior edge
exactly twice. -/
theorem sum_edgeEndpointIncidenceMatrix_mulVec_eq_two_mul_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (x : R.edgeFinset → ℂ) :
    (∑ u, (edgeEndpointIncidenceMatrix R).mulVec x u) =
      2 * ∑ a, x a := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ u, edgeEndpointIncidenceMatrix R u a * x a) =
        ∑ a, (∑ u, edgeEndpointIncidenceMatrix R u a) * x a := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_mul]
    _ = ∑ a, 2 * x a := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      unfold edgeEndpointIncidenceMatrix
      simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [show (Finset.univ.filter fun u : V ↦ u ∈ a.1.toFinset) =
          a.1.toFinset by ext u; simp]
      exact_mod_cast R.card_toFinset_mem_edgeFinset a
    _ = 2 * ∑ a, x a := by rw [Finset.mul_sum]

/-- The kernel of endpoint incidence lies in the zero-sum hyperplane. -/
theorem edgeEndpointIncidenceMatrix_kernel_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (x : R.edgeFinset → ℂ)
    (hIx : (edgeEndpointIncidenceMatrix R).mulVec x = 0) :
    ∑ a, x a = 0 := by
  have hsum := congrArg (fun y : V → ℂ ↦ ∑ u, y u) hIx
  rw [sum_edgeEndpointIncidenceMatrix_mulVec_eq_two_mul_sum R x] at hsum
  simp only [Pi.zero_apply, Finset.sum_const_zero] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (by norm_num)

/-- On the zero-sum sector, the squared service equation makes the kernel of
endpoint incidence invariant under the square of the service adjacency. -/
theorem edgeIndexedService_incidenceKernel_sq_invariant_of_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (h c : ℂ)
    (hsq : H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R -
        edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
          Cedge.adjMatrix ℂ =
      (h - c) • edgeIndexedOnesMatrix R)
    (x : R.edgeFinset → ℂ)
    (hIx : (edgeEndpointIncidenceMatrix R).mulVec x = 0)
    (hxsum : ∑ a, x a = 0) :
    (edgeEndpointIncidenceMatrix R).mulVec
      ((Cedge.adjMatrix ℂ).mulVec ((Cedge.adjMatrix ℂ).mulVec x)) = 0 := by
  have happ := congrArg (fun M : Matrix V R.edgeFinset ℂ ↦ M.mulVec x) hsq
  have hJx : (edgeIndexedOnesMatrix R).mulVec x = 0 := by
    funext u
    rw [Matrix.mulVec, dotProduct]
    simp only [edgeIndexedOnesMatrix, one_mul, Pi.zero_apply]
    exact hxsum
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hIx,
    Matrix.mulVec_zero, Matrix.mulVec_zero, zero_sub,
    Matrix.smul_mulVec, hJx, smul_zero] at happ
  simpa using neg_eq_zero.mp happ

/-- Unconditional form: endpoint-incidence kernel vectors are automatically
zero-sum, hence the kernel is invariant under service adjacency squared. -/
theorem edgeIndexedService_incidenceKernel_sq_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (h c : ℂ)
    (hsq : H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R -
        edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
          Cedge.adjMatrix ℂ =
      (h - c) • edgeIndexedOnesMatrix R)
    (x : R.edgeFinset → ℂ)
    (hIx : (edgeEndpointIncidenceMatrix R).mulVec x = 0) :
    (edgeEndpointIncidenceMatrix R).mulVec
      ((Cedge.adjMatrix ℂ).mulVec ((Cedge.adjMatrix ℂ).mulVec x)) = 0 := by
  exact edgeIndexedService_incidenceKernel_sq_invariant_of_sum_zero
    H R Cedge h c hsq x hIx
      (edgeEndpointIncidenceMatrix_kernel_sum_zero R x hIx)

/-- Submodule formulation of the residual-kernel invariance. -/
theorem edgeIndexedService_incidenceKernel_map_sq_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (h c : ℂ)
    (hsq : H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R -
        edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
          Cedge.adjMatrix ℂ =
      (h - c) • edgeIndexedOnesMatrix R) :
    (LinearMap.ker (edgeEndpointIncidenceMatrix R).mulVecLin).map
        ((Cedge.adjMatrix ℂ).mulVecLin.comp
          (Cedge.adjMatrix ℂ).mulVecLin) ≤
      LinearMap.ker (edgeEndpointIncidenceMatrix R).mulVecLin := by
  rintro y ⟨x, hx, rfl⟩
  change (edgeEndpointIncidenceMatrix R).mulVec x = 0 at hx
  change (edgeEndpointIncidenceMatrix R).mulVec
    ((Cedge.adjMatrix ℂ).mulVec ((Cedge.adjMatrix ℂ).mulVec x)) = 0
  exact edgeIndexedService_incidenceKernel_sq_invariant
    H R Cedge h c hsq x hx

/-- In the h305 dimensions, injectivity of endpoint summation makes the
residual incidence kernel exactly 32-dimensional. -/
theorem edgeEndpointIncidenceMatrix_kernel_finrank_thirtyTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hVcard : Fintype.card V = 16)
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hinj : Function.Injective (edgeEndpointSumVector R)) :
    Module.finrank ℂ
      (LinearMap.ker (edgeEndpointIncidenceMatrix R).mulVecLin) = 32 := by
  let I := edgeEndpointIncidenceMatrix R
  have hinjT : Function.Injective I.transpose.mulVecLin := by
    intro f g hfg
    apply hinj
    exact hfg
  have hkerT : LinearMap.ker I.transpose.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjT
  have hrankNullT :=
    LinearMap.finrank_range_add_finrank_ker I.transpose.mulVecLin
  have hrankT : I.transpose.rank = 16 := by
    rw [Matrix.rank]
    rw [hkerT] at hrankNullT
    simpa [Module.finrank_fintype_fun_eq_card ℂ, hVcard] using hrankNullT
  have hrankI : I.rank = 16 := by
    rw [← Matrix.rank_transpose]
    exact hrankT
  have hrankNull := LinearMap.finrank_range_add_finrank_ker I.mulVecLin
  rw [← Matrix.rank, hrankI,
    Module.finrank_fintype_fun_eq_card ℂ, hEcard] at hrankNull
  have hk : Module.finrank ℂ (LinearMap.ker I.mulVecLin) = 32 := by
    omega
  simpa [I] using hk

end

end Erdos85

#print axioms
  Erdos85.edgeIndexedService_incidenceKernel_sq_invariant_of_sum_zero
#print axioms Erdos85.edgeIndexedService_incidenceKernel_sq_invariant
#print axioms Erdos85.edgeIndexedService_incidenceKernel_map_sq_le
#print axioms
  Erdos85.edgeEndpointIncidenceMatrix_kernel_finrank_thirtyTwo
