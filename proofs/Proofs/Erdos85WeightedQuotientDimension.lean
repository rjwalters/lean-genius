import Proofs.Erdos85MixedSectorMassQuotient
import Proofs.Erdos85QuadraticDimension

/-!
# Odd dimension of a nonsquare weighted Moore quotient

A weighted quotient satisfying `Q² = aI + 1rᵀ` splits into its constant
eigenline and a complementary kernel on which the square is `aI`.  When `a`
is a rational nonsquare, that complement has even dimension, so the whole
quotient has odd dimension.
-/

namespace Erdos85

noncomputable section

/-- A weighted Moore quotient with nonsquare transverse scalar has odd size. -/
theorem Matrix.odd_card_of_sq_weightedRankOne_of_nonsquare
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℚ) (r : I → ℚ) (d : ℚ) (a : ℕ)
    (hR : (∑ i, r i) ≠ 0)
    (hrow : ∀ i, ∑ j, Q i j = d)
    (hleft : ∀ j, ∑ i, r i * Q i j = d * r j)
    (hsq : Q * Q = (a : ℚ) • (1 : Matrix I I ℚ) +
      Matrix.of (fun _ j ↦ r j))
    (ha : ¬ IsSquare a) : Odd (Fintype.card I) := by
  let P := weightedConstantProjection r
  have hPmat : IsIdempotentElem P :=
    weightedConstantProjection_isIdempotent r hR
  have hQPmat : Q * P = d • P := by
    ext i j
    simp only [Matrix.mul_apply, P, weightedConstantProjection,
      Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.sum_mul, hrow]
  have hPQmat : P * Q = d • P := by
    ext i j
    simp only [Matrix.mul_apply, P, weightedConstantProjection,
      Matrix.smul_apply, smul_eq_mul]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hleft]
    ring
  have hcommMat : Q * P = P * Q := hQPmat.trans hPQmat.symm
  have hrankMat : Matrix.of (fun _ j ↦ r j) = (∑ i, r i) • P := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, P,
      weightedConstantProjection]
    field_simp
  have hP : IsIdempotentElem P.toLin' := by
    rw [IsIdempotentElem]
    simpa only [Module.End.mul_eq_comp, Matrix.toLin'_mul] using
      congrArg Matrix.toLin' hPmat
  have hcomm : Q.toLin' * P.toLin' = P.toLin' * Q.toLin' := by
    have h := congrArg Matrix.toLin' hcommMat
    simpa [Module.End.mul_eq_comp, Matrix.toLin'_mul] using h
  have hQsq : Q.toLin' * Q.toLin' =
      (a : ℚ) • LinearMap.id + (∑ i, r i) • P.toLin' := by
    have h := congrArg Matrix.toLin' hsq
    rw [hrankMat] at h
    simpa [Module.End.mul_eq_comp, Matrix.toLin'_mul, Matrix.toLin'_one,
      map_add, map_smul] using h
  let W := LinearMap.ker P.toLin'
  let hW := mapsTo_ker_of_commute Q.toLin' P.toLin' hcomm
  have hWsq : (Q.toLin'.restrict hW) * (Q.toLin'.restrict hW) =
      (a : ℚ) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hs := LinearMap.congr_fun hQsq x
    have hx := x.property
    rw [LinearMap.mem_ker] at hx
    simpa [LinearMap.restrict_apply, Module.End.mul_apply, hx] using hs
  have hWeven : Even (Module.finrank ℚ W) :=
    LinearMap.even_finrank_of_sq_eq_nonsquare_nat
      (Q.toLin'.restrict hW) a ha hWsq
  have htraceP : LinearMap.trace ℚ (I → ℚ) P.toLin' = 1 := by
    rw [Matrix.trace_toLin'_eq]
    exact weightedConstantProjection_trace r hR
  have hproj := LinearMap.IsIdempotentElem.isProj_range P.toLin' hP
  have hrange : Module.finrank ℚ (LinearMap.range P.toLin') = 1 := by
    have ht : LinearMap.trace ℚ (I → ℚ) P.toLin' =
        (Module.finrank ℚ (LinearMap.range P.toLin') : ℚ) := hproj.trace
    rw [htraceP] at ht
    exact_mod_cast ht.symm
  have hranknull := P.toLin'.finrank_range_add_finrank_ker
  rw [hrange, Module.finrank_pi] at hranknull
  have hranknullW : 1 + Module.finrank ℚ W = Fintype.card I := by
    simpa [W] using hranknull
  obtain ⟨k, hk⟩ := hWeven
  refine ⟨k, ?_⟩
  change Fintype.card I = 2 * k + 1
  calc
    Fintype.card I = 1 + Module.finrank ℚ W := hranknullW.symm
    _ = 1 + (k + k) := by rw [hk]
    _ = 2 * k + 1 := by omega

end

end Erdos85
