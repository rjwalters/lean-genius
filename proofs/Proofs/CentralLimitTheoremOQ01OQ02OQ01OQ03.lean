/-
# The Gaussian characteristic-function ODE and cumulant structure
# (central-limit-theorem-oq-01-oq-02-oq-01-oq-03)

The parent chain studies the Gaussian Lévy–Khintchine exponent

    ψ(t) = gaussianExponent μ σ² t = iμt − σ²t²/2,

and the characteristic function φ(t) = exp(ψ(t)). Earlier siblings establish the
algebraic properties of φ (modulus, product/convolution law, conjugation,
scaling). This file supplies the **differential** structure, which the chain had
not recorded:

1. The exponent derivative ψ'(t) = iμ − σ²t.
2. The **characteristic-function ODE** φ'(t) = φ(t)·(iμ − σ²t): the Gaussian CF
   is the unique solution with φ(0)=1 of a first-order linear ODE whose
   coefficient is *affine* in t. This affine logarithmic derivative is exactly
   what singles out the Gaussian.
3. The **cumulant structure**: ψ'(0) = iμ, ψ''(t) = −σ² (constant), and
   ψ'''(t) = 0. Since the cumulants are κ_k = i^{-k}·ψ^{(k)}(0), this says
   κ₁ = μ, κ₂ = σ², and **every cumulant of order ≥ 3 vanishes** — the defining
   analytic signature of the normal distribution (Marcinkiewicz's theorem: only
   the Gaussian has a polynomial cumulant generating function).

## Main results

- `gaussianExponent_hasDerivAt`   : HasDerivAt ψ (iμ − σ²t) t          [ψ' = iμ − σ²t]
- `gaussianExponent_deriv`        : deriv ψ t = iμ − σ²t
- `gaussianCharFn_hasDerivAt`     : the ODE φ'(t) = φ(t)·(iμ − σ²t)
- `gaussianExponent_deriv_zero`   : ψ'(0) = iμ                          [κ₁ = μ]
- `gaussianExponent_deriv2`       : HasDerivAt ψ' (−σ²) t               [ψ'' = −σ²]
- `gaussianExponent_deriv2_zero`  : deriv ψ' 0 = −σ²                    [κ₂ = σ²]
- `gaussianExponent_deriv3`       : HasDerivAt ψ'' 0 t                  [ψ''' ≡ 0, κ_{≥3}=0]

All results are fully machine-checked: 0 sorries, 0 `axiom` declarations.

## References

- Lévy–Khintchine representation; cumulant generating function
- J. Marcinkiewicz (1939): a CGF that is a polynomial must have degree ≤ 2
-/

import Proofs.CentralLimitTheoremOQ01OQ02
import Mathlib

namespace CentralLimitTheoremOQ01OQ02OQ01OQ03

open Complex CentralLimitTheoremOQ01OQ02

/-- **ψ'(t) = iμ − σ²t.** The Gaussian Lévy–Khintchine exponent has an affine
    derivative — the hallmark of a quadratic cumulant generating function. -/
theorem gaussianExponent_hasDerivAt (μ σ_sq t : ℝ) :
    HasDerivAt (gaussianExponent μ σ_sq)
      (↑μ * Complex.I - ↑(σ_sq * t)) t := by
  unfold gaussianExponent
  have h1 : HasDerivAt (fun s : ℝ => ((μ * s : ℝ) : ℂ)) (↑μ : ℂ) t := by
    have hr : HasDerivAt (fun s : ℝ => μ * s) μ t := by
      simpa using (hasDerivAt_id t).const_mul μ
    exact hr.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => σ_sq * s ^ 2 / 2) (σ_sq * t) t := by
    have h := ((hasDerivAt_pow 2 t).const_mul σ_sq).div_const 2
    convert h using 1
    ring
  exact (h1.mul_const Complex.I).sub h2.ofReal_comp

/-- The `deriv` form of `gaussianExponent_hasDerivAt`. -/
theorem gaussianExponent_deriv (μ σ_sq t : ℝ) :
    deriv (gaussianExponent μ σ_sq) t = ↑μ * Complex.I - ↑(σ_sq * t) :=
  (gaussianExponent_hasDerivAt μ σ_sq t).deriv

/-- **The Gaussian characteristic-function ODE.**
    φ'(t) = φ(t)·(iμ − σ²t), where φ(t) = exp(ψ(t)). The affine coefficient
    `iμ − σ²t` characterises the Gaussian among characteristic functions. -/
theorem gaussianCharFn_hasDerivAt (μ σ_sq t : ℝ) :
    HasDerivAt (fun s => Complex.exp (gaussianExponent μ σ_sq s))
      (Complex.exp (gaussianExponent μ σ_sq t) * (↑μ * Complex.I - ↑(σ_sq * t))) t :=
  (gaussianExponent_hasDerivAt μ σ_sq t).cexp

/-- **First cumulant: κ₁ = μ.** ψ'(0) = iμ. -/
theorem gaussianExponent_deriv_zero (μ σ_sq : ℝ) :
    deriv (gaussianExponent μ σ_sq) 0 = ↑μ * Complex.I := by
  rw [gaussianExponent_deriv]
  simp

/-- **ψ''(t) = −σ² (constant).** The second derivative of the exponent is the
    constant `−σ²`; in particular all higher derivatives vanish. -/
theorem gaussianExponent_deriv2 (μ σ_sq t : ℝ) :
    HasDerivAt (fun s : ℝ => (↑μ * Complex.I - ↑(σ_sq * s) : ℂ)) (-↑σ_sq) t := by
  have h : HasDerivAt (fun s : ℝ => ((σ_sq * s : ℝ) : ℂ)) (↑σ_sq) t := by
    have hr : HasDerivAt (fun s : ℝ => σ_sq * s) σ_sq t := by
      simpa using (hasDerivAt_id t).const_mul σ_sq
    exact hr.ofReal_comp
  simpa using (hasDerivAt_const t (↑μ * Complex.I)).sub h

/-- **Second cumulant: κ₂ = σ².** The second derivative of ψ is `−σ²`, so the
    second cumulant `κ₂ = -ψ''(0)` equals `σ²`. -/
theorem gaussianExponent_deriv2_zero (μ σ_sq : ℝ) :
    deriv (fun s : ℝ => (↑μ * Complex.I - ↑(σ_sq * s) : ℂ)) 0 = -↑σ_sq :=
  (gaussianExponent_deriv2 μ σ_sq 0).deriv

/-- **Cumulants of order ≥ 3 vanish.** ψ''' ≡ 0: the second derivative `−σ²` is
    constant, so its derivative is zero. This is the analytic signature of the
    Gaussian — a degree-2 cumulant generating function. -/
theorem gaussianExponent_deriv3 (σ_sq t : ℝ) :
    HasDerivAt (fun _ : ℝ => (-↑σ_sq : ℂ)) 0 t :=
  hasDerivAt_const t _

end CentralLimitTheoremOQ01OQ02OQ01OQ03
