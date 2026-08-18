import Proofs.Erdos85PrimeFourierConvolution
import Mathlib.LinearAlgebra.Trace

/-!
# Trace in the square quadratic branch

If `T²=s²I` with `s≠0`, then `(I+s⁻¹T)/2` is the projector onto the
`+s` eigenspace.  In even dimension this makes `trace T` twice an integral
multiple of `s`.
-/

namespace Erdos85

noncomputable section

theorem LinearMap.exists_int_trace_eq_two_mul_of_sq_eq_sq
    {K E : Type*} [Field K] [CharZero K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (T : E →ₗ[K] E) (s : K) (hs : s ≠ 0)
    (hsq : T * T = (s * s) • LinearMap.id)
    (heven : Even (Module.finrank K E)) :
    ∃ u : ℤ, LinearMap.trace K E T = 2 * (u : K) * s := by
  let S : E →ₗ[K] E := s⁻¹ • T
  have hSsq : S * S = LinearMap.id := by
    ext x
    have hx := LinearMap.congr_fun hsq x
    simp only [Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hx ⊢
    dsimp only [S]
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [hx]
    rw [smul_smul]
    convert one_smul K x using 1
    field_simp
  let P : E →ₗ[K] E := (2 : K)⁻¹ • (LinearMap.id + S)
  have hP : IsIdempotentElem P := by
    ext x
    have hx := LinearMap.congr_fun hSsq x
    simp only [Module.End.mul_apply, LinearMap.id_apply] at hx
    simp [P, map_add, map_smul, hx]
    module
  have htraceP : LinearMap.trace K E P =
      (Module.finrank K (LinearMap.range P) : K) :=
    (LinearMap.IsIdempotentElem.isProj_range P hP).trace
  obtain ⟨m, hm⟩ := heven
  let u : ℤ := (Module.finrank K (LinearMap.range P) : ℤ) - m
  refine ⟨u, ?_⟩
  have htraceExpanded : LinearMap.trace K E P =
      (2 : K)⁻¹ * ((Module.finrank K E : K) + s⁻¹ *
        LinearMap.trace K E T) := by
    simp [P, S, map_add, map_smul]
    ring
  rw [htraceP] at htraceExpanded
  have hmK : (Module.finrank K E : K) = 2 * (m : K) := by
    have hm' : Module.finrank K E = 2 * m := by omega
    exact_mod_cast hm'
  rw [hmK] at htraceExpanded
  dsimp only [u]
  push_cast
  have htraceExpanded' := htraceExpanded
  field_simp [hs] at htraceExpanded'
  have htraceSolved : LinearMap.trace K E T =
      2 * (Module.finrank K (LinearMap.range P) : K) * s -
        2 * (m : K) * s := by
    rw [eq_sub_iff_add_eq]
    simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using
      htraceExpanded'.symm
  rw [htraceSolved]
  ring

/-- If the trace of `T` is twice a prescribed Fourier coefficient `H`, the
square branch writes `H²` as an integral square times the scalar `s²`.

This is the form needed by the frequency-pair argument: the graph-facing
trace calculation supplies `trace T = 2 * H`, while the operator restriction
supplies `T² = s² I`. -/
theorem LinearMap.exists_int_fourier_sq_eq_of_trace_eq_two_mul
    {K E : Type*} [Field K] [CharZero K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (T : E →ₗ[K] E) (s H : K) (hs : s ≠ 0)
    (hsq : T * T = (s * s) • LinearMap.id)
    (heven : Even (Module.finrank K E))
    (htrace : LinearMap.trace K E T = 2 * H) :
    ∃ u : ℤ, H * H = ((u : K) * (u : K)) * (s * s) := by
  obtain ⟨u, hu⟩ :=
    LinearMap.exists_int_trace_eq_two_mul_of_sq_eq_sq T s hs hsq heven
  refine ⟨u, ?_⟩
  have htwo : (2 : K) * H = (2 : K) * ((u : K) * s) := by
    calc
      (2 : K) * H = LinearMap.trace K E T := htrace.symm
      _ = 2 * (u : K) * s := hu
      _ = (2 : K) * ((u : K) * s) := by ring
  have hH : H = (u : K) * s :=
    mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0) htwo
  rw [hH]
  ring

end

end Erdos85
