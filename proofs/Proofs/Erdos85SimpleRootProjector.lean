import Proofs.Erdos85QuadraticTrace
import Proofs.Erdos85RationalPrimaryTraceSplit
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # A polynomial projector onto a simple root sector

If `(X - μ) p` annihilates an operator and `p(μ) ≠ 0`, then the normalized
operator `p(T) / p(μ)` is the projector onto the `μ`-eigenspace.  This turns
finite spectral records into small exact polynomial certificates.
-/

namespace Erdos85

open Polynomial

noncomputable section

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- The normalized complementary-factor projector. -/
def simpleRootProjector (T : E →ₗ[K] E) (μ : K) (p : Polynomial K) :
    E →ₗ[K] E := (p.eval μ)⁻¹ • Polynomial.aeval T p

/-- The normalized complementary factor lands in the linear `μ`-sector. -/
theorem simpleRootProjector_mem_ker
    (T : E →ₗ[K] E) (μ : K) (p : Polynomial K)
    (hann : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C μ) * p) = 0) (v : E) :
    simpleRootProjector T μ p v ∈
      LinearMap.ker
        (Polynomial.aeval T (Polynomial.X - Polynomial.C μ)) := by
  rw [LinearMap.mem_ker]
  simp only [simpleRootProjector, LinearMap.smul_apply, map_smul]
  rw [← Module.End.mul_apply, ← map_mul, hann]
  simp

/-- On the `μ`-sector the normalized complementary factor is the identity. -/
theorem simpleRootProjector_apply_of_mem_ker
    (T : E →ₗ[K] E) (μ : K) (p : Polynomial K)
    (hp : p.eval μ ≠ 0) {v : E}
    (hv : v ∈ LinearMap.ker
      (Polynomial.aeval T (Polynomial.X - Polynomial.C μ))) :
    simpleRootProjector T μ p v = v := by
  have hTv : T v = μ • v := by
    rw [LinearMap.mem_ker, aeval_X_sub_C_eq, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hv
    exact hv
  rw [simpleRootProjector, LinearMap.smul_apply,
    Module.End.aeval_apply_of_mem_apply_eq_smul hTv]
  rw [smul_smul, inv_mul_cancel₀ hp, one_smul]

/-- The normalized complementary factor is idempotent. -/
theorem simpleRootProjector_isIdempotent
    (T : E →ₗ[K] E) (μ : K) (p : Polynomial K)
    (hann : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C μ) * p) = 0)
    (hp : p.eval μ ≠ 0) :
    simpleRootProjector T μ p * simpleRootProjector T μ p =
      simpleRootProjector T μ p := by
  apply LinearMap.ext
  intro v
  exact simpleRootProjector_apply_of_mem_ker T μ p hp
    (simpleRootProjector_mem_ker T μ p hann v)

/-- The range is exactly the `μ` primary sector. -/
theorem range_simpleRootProjector_eq_ker
    (T : E →ₗ[K] E) (μ : K) (p : Polynomial K)
    (hann : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C μ) * p) = 0)
    (hp : p.eval μ ≠ 0) :
    LinearMap.range (simpleRootProjector T μ p) =
      LinearMap.ker
        (Polynomial.aeval T (Polynomial.X - Polynomial.C μ)) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact simpleRootProjector_mem_ker T μ p hann w
  · intro hv
    exact ⟨v, simpleRootProjector_apply_of_mem_ker T μ p hp hv⟩

/-- Any operator commuting with `T` commutes with its simple-root projector. -/
theorem commute_simpleRootProjector
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (μ : K) (p : Polynomial K) :
    S * simpleRootProjector T μ p = simpleRootProjector T μ p * S := by
  let a := (p.eval μ)⁻¹
  calc
    S * simpleRootProjector T μ p =
        a • (S * Polynomial.aeval T p) := by
      rw [simpleRootProjector, Algebra.mul_smul_comm]
    _ = a • (Polynomial.aeval T p * S) := by
      rw [commute_aeval_right S T hcomm p]
    _ = simpleRootProjector T μ p * S := by
      rw [simpleRootProjector, Algebra.smul_mul_assoc]

/-- The trace on the simple-root sector is computed by multiplying by the
explicit polynomial projector. -/
theorem trace_kerAevalRestrict_eq_trace_mul_simpleRootProjector
    {E₂ : Type*} [AddCommGroup E₂] [Module ℚ E₂]
    [FiniteDimensional ℚ E₂]
    (S T : E₂ →ₗ[ℚ] E₂) (hcomm : S * T = T * S)
    (μ : ℚ) (p : Polynomial ℚ)
    (hann : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C μ) * p) = 0)
    (hp : p.eval μ ≠ 0) :
    LinearMap.trace ℚ _ (kerAevalRestrict S T hcomm
      (Polynomial.X - Polynomial.C μ)) =
      LinearMap.trace ℚ E₂ (S * simpleRootProjector T μ p) := by
  let P := simpleRootProjector T μ p
  have hP : P * P = P := simpleRootProjector_isIdempotent T μ p hann hp
  have hP' : IsIdempotentElem P := hP
  have hSP : S * P = P * S := commute_simpleRootProjector S T hcomm μ p
  have htrace := trace_restrict_range_eq_trace_mul_of_idempotent S P hP' hSP
  let Kμ := LinearMap.ker
    (Polynomial.aeval T (Polynomial.X - Polynomial.C μ))
  have hrange : LinearMap.range P = Kμ :=
    range_simpleRootProjector_eq_ker T μ p hann hp
  let e : LinearMap.range P ≃ₗ[ℚ] Kμ :=
    LinearEquiv.ofEq (LinearMap.range P) Kμ hrange
  calc
    LinearMap.trace ℚ Kμ
        (kerAevalRestrict S T hcomm
          (Polynomial.X - Polynomial.C μ)) =
        LinearMap.trace ℚ Kμ
          (e.conj (S.restrict (mapsTo_range_of_commute S P hSP))) := by
            congr 1
    _ = LinearMap.trace ℚ (LinearMap.range P)
          (S.restrict (mapsTo_range_of_commute S P hSP)) :=
      LinearMap.trace_conj' _ e
    _ = LinearMap.trace ℚ E₂ (S * P) := htrace

/-- Minimal exact certificate consumer for the order-64 `μ = 3` ledger.
It suffices to check one polynomial annihilation, one nonzero scalar, and one
unnormalized trace identity; normalization then forces local sector trace
`-2`. -/
theorem trace_three_sector_eq_neg_two_of_polynomial_certificate
    {E₂ : Type*} [AddCommGroup E₂] [Module ℚ E₂]
    [FiniteDimensional ℚ E₂]
    (S T : E₂ →ₗ[ℚ] E₂) (hcomm : S * T = T * S)
    (p : Polynomial ℚ)
    (hann : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C (3 : ℚ)) * p) = 0)
    (hp : p.eval 3 ≠ 0)
    (htrace : LinearMap.trace ℚ E₂ (S * Polynomial.aeval T p) =
      (-2 : ℚ) * p.eval 3) :
    LinearMap.trace ℚ _
      (kerAevalRestrict S T hcomm
        (Polynomial.X - Polynomial.C (3 : ℚ))) = -2 := by
  rw [trace_kerAevalRestrict_eq_trace_mul_simpleRootProjector
    S T hcomm 3 p hann hp]
  rw [simpleRootProjector, Algebra.mul_smul_comm, map_smul, htrace]
  change (p.eval 3)⁻¹ * ((-2 : ℚ) * p.eval 3) = -2
  field_simp

end

end Erdos85
