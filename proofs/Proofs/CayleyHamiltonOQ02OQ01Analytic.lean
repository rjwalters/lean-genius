import Mathlib

/-
# Putzer's Algorithm — the Scalar ODE Coefficients (Analytic Layer, Part 1)

The companion file `CayleyHamiltonOQ02OQ01.lean` proves the purely *algebraic* core of
Putzer's algorithm: the telescoping identity `A·ρ_k = ρ_{k+1} + λ_k•ρ_k`, the Cayley–Hamilton
truncation `ρ_n = 0`, and the assembled algebraic IVP

  `A · M = ∑_k (λ_k P_k + P_{k-1})•ρ_k`     and     `M(0) = 1`,        `M := ∑_k P_k•ρ_k`,

*for any* coefficient family `P` with the Putzer initial data.  What remained open was the
**analytic** half: exhibiting actual coefficient *functions* `P_k : ℝ → ℂ` that solve the
triangular linear ODE system

  `Ṗ_0 = λ_0 P_0,          P_0(0) = 1,`
  `Ṗ_{k+1} = λ_{k+1} P_{k+1} + P_k,   P_{k+1}(0) = 0.`

This file constructs those functions and proves their derivative relations and initial
conditions.  The construction is the classical variation-of-parameters recursion

  `P_0(t) = e^{λ_0 t},`
  `P_{k+1}(t) = e^{λ_{k+1} t} · ∫_0^t e^{-λ_{k+1} s} P_k(s) ds.`

**Main results**
* `scoeff`                    : the coefficient functions, by the recursion above.
* `scoeff_zero_zero`          : `P_0(0) = 1`.
* `scoeff_succ_zero`          : `P_{k+1}(0) = 0`.
* `scoeff_continuous`         : every `P_k` is continuous (needed to differentiate the integral).
* `scoeff_hasDerivAt_zero`    : `Ṗ_0(t) = λ_0 · P_0(t)`.
* `scoeff_hasDerivAt_succ`    : `Ṗ_{k+1}(t) = λ_{k+1} · P_{k+1}(t) + P_k(t)`.

Together with the algebraic IVP of the companion file, these are exactly the ODE-coefficient
facts the deferred matrix-ODE-uniqueness step will feed into `NormedSpace.exp`.  The uniqueness
step (`ODE_solution_unique` for the matrix-valued field `M ↦ A·M`) is the only remaining piece.
-/

namespace PutzerMatrixExp

open Complex intervalIntegral MeasureTheory

/-- The Putzer scalar coefficients as functions `ℝ → ℂ`, built by the classical
variation-of-parameters recursion
`P_0(t) = e^{λ_0 t}`, `P_{k+1}(t) = e^{λ_{k+1} t} · ∫_0^t e^{-λ_{k+1} s} P_k(s) ds`. -/
noncomputable def scoeff (lam : ℕ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun t => Complex.exp (lam 0 * t)
  | (k + 1) => fun t =>
      Complex.exp (lam (k + 1) * t) *
        ∫ s in (0:ℝ)..t, Complex.exp (-(lam (k + 1)) * s) * scoeff lam k s

@[simp] lemma scoeff_zero_apply (lam : ℕ → ℂ) (t : ℝ) :
    scoeff lam 0 t = Complex.exp (lam 0 * t) := rfl

lemma scoeff_succ_apply (lam : ℕ → ℂ) (k : ℕ) (t : ℝ) :
    scoeff lam (k + 1) t =
      Complex.exp (lam (k + 1) * t) *
        ∫ s in (0:ℝ)..t, Complex.exp (-(lam (k + 1)) * s) * scoeff lam k s := rfl

/-- Initial condition for the leading coefficient: `P_0(0) = 1`. -/
@[simp] lemma scoeff_zero_zero (lam : ℕ → ℂ) : scoeff lam 0 0 = 1 := by
  simp

/-- Initial condition for the subordinate coefficients: `P_{k+1}(0) = 0`
(the integral over the degenerate interval `[0,0]` vanishes). -/
@[simp] lemma scoeff_succ_zero (lam : ℕ → ℂ) (k : ℕ) : scoeff lam (k + 1) 0 = 0 := by
  simp [scoeff_succ_apply]

/-- The elementary building block `t ↦ e^{μ t}` (as a function `ℝ → ℂ`) has derivative
`μ · e^{μ t}`. -/
lemma hasDerivAt_cexp_mul (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (μ * (t : ℂ))) (μ * Complex.exp (μ * (t : ℂ))) t := by
  have hofReal : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
    simpa using Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ => μ * (t : ℂ)) μ t := by
    simpa using hofReal.const_mul μ
  have := hlin.cexp
  simpa [mul_comm] using this

/-- Continuity of every scalar coefficient `P_k`. Proved by induction: the base case is a
composition of continuous functions, and the successor case is continuous because it is
differentiable everywhere (via `scoeff_hasDerivAt_succ`, whose derivative computation uses only
this continuity at the previous level). -/
lemma scoeff_continuous (lam : ℕ → ℂ) : ∀ k, Continuous (scoeff lam k)
  | 0 => by
      simpa [scoeff_zero_apply] using
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))
  | (k + 1) => by
      have hk : Continuous (scoeff lam k) := scoeff_continuous lam k
      -- integrand `s ↦ e^{-λ s} · P_k(s)` is continuous
      have hInt : Continuous
          (fun s : ℝ => Complex.exp (-(lam (k + 1)) * s) * scoeff lam k s) :=
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal)).mul hk
      -- primitive `t ↦ ∫_0^t (…)` is continuous
      have hPrim : Continuous
          (fun t : ℝ => ∫ s in (0:ℝ)..t,
            Complex.exp (-(lam (k + 1)) * s) * scoeff lam k s) := by
        apply continuous_primitive
        intro a b
        exact (hInt.intervalIntegrable a b)
      have hExp : Continuous (fun t : ℝ => Complex.exp (lam (k + 1) * (t : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      exact hExp.mul hPrim

/-- Derivative relation for the leading coefficient: `Ṗ_0(t) = λ_0 · P_0(t)`. -/
lemma scoeff_hasDerivAt_zero (lam : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (scoeff lam 0) (lam 0 * scoeff lam 0 t) t := by
  simpa [scoeff_zero_apply] using hasDerivAt_cexp_mul (lam 0) t

/-- Derivative relation for the subordinate coefficients:
`Ṗ_{k+1}(t) = λ_{k+1} · P_{k+1}(t) + P_k(t)`.

This is the variation-of-parameters computation: differentiating
`P_{k+1}(t) = e^{λ t} · g(t)` with `g(t) = ∫_0^t e^{-λ s} P_k(s) ds` gives, by the product rule
and the fundamental theorem of calculus (`g'(t) = e^{-λ t} P_k(t)`),

  `Ṗ_{k+1}(t) = λ e^{λ t} g(t) + e^{λ t} e^{-λ t} P_k(t) = λ P_{k+1}(t) + P_k(t)`,

using `e^{λ t} e^{-λ t} = 1`. -/
lemma scoeff_hasDerivAt_succ (lam : ℕ → ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (scoeff lam (k + 1))
      (lam (k + 1) * scoeff lam (k + 1) t + scoeff lam k t) t := by
  -- the integrand `s ↦ e^{-λ s} · P_k(s)`, continuous everywhere
  have hFcont : Continuous
      (fun s : ℝ => Complex.exp (-(lam (k + 1)) * (s : ℂ)) * scoeff lam k s) :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (scoeff_continuous lam k)
  -- derivative of the exponential prefactor `e^{λ t}`
  have hExp : HasDerivAt (fun u : ℝ => Complex.exp (lam (k + 1) * (u : ℂ)))
      (lam (k + 1) * Complex.exp (lam (k + 1) * (t : ℂ))) t :=
    hasDerivAt_cexp_mul (lam (k + 1)) t
  -- derivative of the primitive `t ↦ ∫_0^t e^{-λ s} P_k(s) ds` by the FTC
  have hPrim : HasDerivAt
      (fun u : ℝ => ∫ s in (0:ℝ)..u, Complex.exp (-(lam (k + 1)) * (s : ℂ)) * scoeff lam k s)
      (Complex.exp (-(lam (k + 1)) * (t : ℂ)) * scoeff lam k t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hFcont.intervalIntegrable 0 t
    · exact hFcont.stronglyMeasurableAtFilter _ _
    · exact hFcont.continuousAt
  -- `e^{λ t} · e^{-λ t} = 1`
  have hcancel :
      Complex.exp (lam (k + 1) * (t : ℂ)) * Complex.exp (-(lam (k + 1)) * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add, show lam (k + 1) * (t : ℂ) + -(lam (k + 1)) * (t : ℂ) = 0 from by ring,
      Complex.exp_zero]
  -- product rule; `scoeff lam (k+1)` is definitionally the product being differentiated
  have hmul : HasDerivAt (scoeff lam (k + 1))
      (lam (k + 1) * Complex.exp (lam (k + 1) * (t : ℂ)) *
          (∫ s in (0:ℝ)..t, Complex.exp (-(lam (k + 1)) * (s : ℂ)) * scoeff lam k s)
        + Complex.exp (lam (k + 1) * (t : ℂ)) *
          (Complex.exp (-(lam (k + 1)) * (t : ℂ)) * scoeff lam k t)) t :=
    hExp.mul hPrim
  -- rewrite the derivative to `λ · P_{k+1} + P_k`
  have hval :
      lam (k + 1) * Complex.exp (lam (k + 1) * (t : ℂ)) *
          (∫ s in (0:ℝ)..t, Complex.exp (-(lam (k + 1)) * (s : ℂ)) * scoeff lam k s)
        + Complex.exp (lam (k + 1) * (t : ℂ)) *
          (Complex.exp (-(lam (k + 1)) * (t : ℂ)) * scoeff lam k t)
      = lam (k + 1) * scoeff lam (k + 1) t + scoeff lam k t := by
    rw [scoeff_succ_apply]
    linear_combination (scoeff lam k t) * hcancel
  rwa [hval] at hmul

end PutzerMatrixExp
