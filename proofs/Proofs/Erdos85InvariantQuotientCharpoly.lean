import Proofs.Erdos85EdgeIndexedServiceQuotientOperator
import Proofs.Erdos85InvariantCharpolyDivisibility
import Mathlib.LinearAlgebra.Determinant

/-!
# Characteristic polynomials across an invariant subspace and quotient

This complements the invariant-restriction divisibility theorem with the
exact upper-triangular factorization: the second factor is the induced
endomorphism on the quotient by the invariant subspace.
-/

namespace Erdos85

noncomputable section

open LinearMap Module Matrix

/-- An endomorphism preserving `W` has characteristic polynomial equal to
the product of its restriction to `W` and its induced quotient operator. -/
theorem charpoly_eq_mul_restrict_mapQ
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (T : E →ₗ[K] E) (W : Submodule K E)
    (hW : W ≤ W.comap T) :
    T.charpoly = (T.restrict hW).charpoly * (W.mapQ W T hW).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex K W
  let bW : Basis m K W := Module.Free.chooseBasis K W
  let n := Module.Free.ChooseBasisIndex K (E ⧸ W)
  let bQ : Basis n K (E ⧸ W) := Module.Free.chooseBasis K (E ⧸ W)
  let b := Basis.sumQuot bW bQ
  let A : Matrix m m K := LinearMap.toMatrix bW bW (T.restrict hW)
  let B : Matrix m n K := Matrix.of fun i l ↦
    (b.repr (T (b (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n K := LinearMap.toMatrix bQ bQ (W.mapQ W T hW)
  have hmatrix : LinearMap.toMatrix b b T = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
        cases v with
        | inl k =>
            simp only [b, Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁,
              A, LinearMap.toMatrix_apply]
            apply Basis.sumQuot_repr_inl_of_mem
        | inr l =>
            simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
        cases v with
        | inl k =>
            suffices W.mkQ (T (bW k)) = 0 by
              simp [LinearMap.toMatrix_apply, b, this]
            rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
            exact hW (Submodule.coe_mem (bW k))
        | inr l =>
            simp only [LinearMap.toMatrix_apply, Basis.sumQuot_repr_inr,
              Matrix.fromBlocks_apply₂₂, b, D]
            rw [← Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
            simp
  rw [← LinearMap.charpoly_toMatrix T b,
    ← LinearMap.charpoly_toMatrix (T.restrict hW) bW,
    ← LinearMap.charpoly_toMatrix (W.mapQ W T hW) bQ,
    hmatrix]
  exact Matrix.charpoly_fromBlocks_zero₂₁ A B D

/-- For an edge-indexed service graph, the ambient characteristic polynomial
splits exactly into the incidence-kernel restriction and the induced
16-dimensional quotient factor. -/
theorem edgeIndexedService_charpoly_eq_residual_mul_quotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hVcard : Fintype.card V = 16)
    (hEcard : Fintype.card R.edgeFinset = 48)
    (hinj : Function.Injective (edgeEndpointSumVector R)) :
    let I := (edgeEndpointIncidenceMatrix R).mulVecLin
    let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
    let W := LinearMap.ker I
    let hW : W ≤ W.comap T := by
      intro x hx
      exact edgeIndexedService_incidenceKernel_invariant
        H R Cedge hservice x hx
    T.charpoly = (T.restrict hW).charpoly * (W.mapQ W T hW).charpoly ∧
      (T.restrict hW).charpoly.natDegree = 32 ∧
      (W.mapQ W T hW).charpoly.natDegree = 16 := by
  classical
  dsimp only
  let I := (edgeEndpointIncidenceMatrix R).mulVecLin
  let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
  let W := LinearMap.ker I
  let hW : W ≤ W.comap T := by
    intro x hx
    exact edgeIndexedService_incidenceKernel_invariant
      H R Cedge hservice x hx
  have hfactor := charpoly_eq_mul_restrict_mapQ T W hW
  have hres : (T.restrict hW).charpoly.natDegree = 32 := by
    rw [LinearMap.charpoly_natDegree]
    simpa [W, I] using
      edgeEndpointIncidenceMatrix_kernel_finrank_thirtyTwo
        R hVcard hEcard hinj
  have hquot : (W.mapQ W T hW).charpoly.natDegree = 16 := by
    rw [LinearMap.charpoly_natDegree]
    have hdim := W.finrank_quotient_add_finrank
    rw [show Module.finrank ℂ (R.edgeFinset → ℂ) = 48 by
      simpa [Module.finrank_fintype_fun_eq_card ℂ] using hEcard,
      show Module.finrank ℂ W = 32 by
        simpa [W, I] using
          edgeEndpointIncidenceMatrix_kernel_finrank_thirtyTwo
            R hVcard hEcard hinj] at hdim
    omega
  exact ⟨hfactor, hres, hquot⟩

end

end Erdos85

#print axioms Erdos85.charpoly_eq_mul_restrict_mapQ
#print axioms
  Erdos85.edgeIndexedService_charpoly_eq_residual_mul_quotient
