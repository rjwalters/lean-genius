import Proofs.Erdos85InvariantQuotientCharpoly

/-! # Characteristic splitting through a surjective intertwiner -/

namespace Erdos85

noncomputable section

open LinearMap Module Matrix

/-- A surjective intertwiner identifies the induced quotient operator with
the target operator.  Consequently the source characteristic polynomial is
the kernel-restriction factor times the target characteristic polynomial. -/
theorem charpoly_eq_mul_restrict_of_surjective_intertwiner
    {K E F : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (T : Module.End K E) (S : Module.End K F) (q : E →ₗ[K] F)
    (hq : Function.Surjective q)
    (hinter : q.comp T = S.comp q) :
    let W := LinearMap.ker q
    let hW : W ≤ W.comap T := by
      intro x hx
      change q x = 0 at hx
      change q (T x) = 0
      have := LinearMap.congr_fun hinter x
      simpa [LinearMap.comp_apply, hx] using this
    T.charpoly = (T.restrict hW).charpoly * S.charpoly := by
  classical
  dsimp only
  let W := LinearMap.ker q
  let hW : W ≤ W.comap T := by
    intro x hx
    change q x = 0 at hx
    change q (T x) = 0
    have h := LinearMap.congr_fun hinter x
    simpa [LinearMap.comp_apply, hx] using h
  let Q : Module.End K (E ⧸ W) := W.mapQ W T hW
  let e : (E ⧸ W) ≃ₗ[K] F := q.quotKerEquivOfSurjective hq
  have hconj : e.conj Q = S := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    have h := LinearMap.congr_fun hinter x
    simpa [e, Q, W, LinearEquiv.conj_apply, LinearMap.comp_apply] using h
  have hfactor := charpoly_eq_mul_restrict_mapQ T W hW
  have hQchar : Q.charpoly = S.charpoly := by
    rw [← hconj]
    exact (e.charpoly_conj Q).symm
  change T.charpoly = (T.restrict hW).charpoly * Q.charpoly at hfactor
  rw [hQchar] at hfactor
  exact hfactor

/-- Injectivity of endpoint summation (the transpose action) implies that
endpoint incidence itself is surjective. -/
theorem edgeEndpointIncidenceMatrix_mulVec_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hinj : Function.Injective (edgeEndpointSumVector R)) :
    Function.Surjective (edgeEndpointIncidenceMatrix R).mulVecLin := by
  let I := edgeEndpointIncidenceMatrix R
  have hinjT : Function.Injective I.transpose.mulVecLin := by
    intro f g hfg
    apply hinj
    exact hfg
  have hkerT : LinearMap.ker I.transpose.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinjT
  have hrankNullT :=
    LinearMap.finrank_range_add_finrank_ker I.transpose.mulVecLin
  have hrankT : I.transpose.rank = Module.finrank ℂ (V → ℂ) := by
    rw [Matrix.rank]
    rw [hkerT] at hrankNullT
    simpa using hrankNullT
  have hrankI : I.rank = Module.finrank ℂ (V → ℂ) := by
    rw [← Matrix.rank_transpose]
    exact hrankT
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank]
  exact hrankI

/-- Exact service characteristic split with the quotient factor identified:
the 16-dimensional quotient is the centered shore operator `(1/2)J-A_H`. -/
theorem edgeIndexedService_charpoly_eq_residual_mul_centeredShore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hinj : Function.Injective (edgeEndpointSumVector R)) :
    let I := (edgeEndpointIncidenceMatrix R).mulVecLin
    let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
    let B : Module.End ℂ (V → ℂ) :=
      ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ).mulVecLin
    let W := LinearMap.ker I
    let hW : W ≤ W.comap T := by
      intro x hx
      exact edgeIndexedService_incidenceKernel_invariant
        H R Cedge hservice x hx
    T.charpoly = (T.restrict hW).charpoly * B.charpoly := by
  classical
  dsimp only
  let I := (edgeEndpointIncidenceMatrix R).mulVecLin
  let T : Module.End ℂ (R.edgeFinset → ℂ) := (Cedge.adjMatrix ℂ).mulVecLin
  let B : Module.End ℂ (V → ℂ) :=
    ((2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ).mulVecLin
  have hsurj : Function.Surjective I :=
    edgeEndpointIncidenceMatrix_mulVec_surjective R hinj
  have hinter : I.comp T = B.comp I := by
    apply LinearMap.ext
    intro x
    exact edgeIndexedService_quotient_intertwining_mulVec
      H R Cedge hservice x
  exact charpoly_eq_mul_restrict_of_surjective_intertwiner
    T B I hsurj hinter

end

end Erdos85

#print axioms Erdos85.charpoly_eq_mul_restrict_of_surjective_intertwiner
#print axioms Erdos85.edgeEndpointIncidenceMatrix_mulVec_surjective
#print axioms
  Erdos85.edgeIndexedService_charpoly_eq_residual_mul_centeredShore
