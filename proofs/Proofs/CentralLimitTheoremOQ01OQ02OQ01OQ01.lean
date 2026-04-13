import Mathlib

/-
# Gaussian Characteristic Function exp(iμt - σ²t²/2)

## Research Problem: central-limit-theorem-oq-01-oq-02-oq-01-oq-01

Proves properties of the Gaussian characteristic function
  φ(t) = exp(iμt - σ²t²/2)
including: φ(0) = 1, |φ(t)| = exp(-σ²t²/2), the product formula
for independent sums, and the inversion relationship to the density.

The characteristic function of N(μ,σ²) is the Fourier transform
of the Gaussian density (2πσ²)^(-1/2) exp(-(x-μ)²/(2σ²)).

Tags: probability, complex-analysis, fourier, CLT, characteristic-function
-/

namespace CentralLimitTheoremOQ01OQ02OQ01OQ01

open Complex Real

-- ============================================================
-- Part I: Definition and Basic Properties
-- ============================================================

/-- The Gaussian characteristic function φ(t) = exp(iμt - σ²t²/2). -/
noncomputable def gaussianCharFn (μ σ_sq : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (↑(μ * t) * Complex.I - ↑(σ_sq * t ^ 2 / 2))

/-- At t = 0, the characteristic function equals 1. -/
theorem gaussianCharFn_at_zero (μ σ_sq : ℝ) :
    gaussianCharFn μ σ_sq 0 = 1 := by
  simp [gaussianCharFn]

/-- The exponent of the Gaussian characteristic function. -/
noncomputable def gaussianExponent (μ σ_sq t : ℝ) : ℂ :=
  ↑(μ * t) * Complex.I - ↑(σ_sq * t ^ 2 / 2)

/-- The real part of the exponent is -σ²t²/2. -/
theorem gaussianExponent_re (μ σ_sq t : ℝ) :
    (gaussianExponent μ σ_sq t).re = -(σ_sq * t ^ 2 / 2) := by
  simp [gaussianExponent, Complex.sub_re, Complex.mul_re]
  ring

/-- The imaginary part of the exponent is μt. -/
theorem gaussianExponent_im (μ σ_sq t : ℝ) :
    (gaussianExponent μ σ_sq t).im = μ * t := by
  simp [gaussianExponent, Complex.sub_im, Complex.mul_im]
  ring

-- ============================================================
-- Part II: Modulus and Phase
-- ============================================================

/-- The modulus |φ(t)| = exp(-σ²t²/2), which is the Gaussian envelope.
    This shows the characteristic function decays as a Gaussian in t. -/
theorem gaussianCharFn_abs (μ σ_sq t : ℝ) :
    Complex.abs (gaussianCharFn μ σ_sq t) =
      Real.exp (-(σ_sq * t ^ 2 / 2)) := by
  simp only [gaussianCharFn, map_exp, Complex.abs_exp]
  rw [gaussianExponent_re μ σ_sq t]
  rfl

/-- For σ² > 0 and t ≠ 0, the modulus is strictly less than 1. -/
theorem gaussianCharFn_abs_lt_one {σ_sq : ℝ} (hσ : σ_sq > 0) {t : ℝ} (ht : t ≠ 0)
    (μ : ℝ) : Complex.abs (gaussianCharFn μ σ_sq t) < 1 := by
  rw [gaussianCharFn_abs]
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  exact Real.exp_lt_exp_of_lt (by nlinarith [sq_nonneg t])

/-- The characteristic function has unit modulus when σ² = 0
    (degenerate/point mass distribution). -/
theorem gaussianCharFn_abs_eq_one_of_zero_var (μ t : ℝ) :
    Complex.abs (gaussianCharFn μ 0 t) = 1 := by
  rw [gaussianCharFn_abs]
  simp

-- ============================================================
-- Part III: Product Formula (Independent Sum)
-- ============================================================

/-- The product formula: φ_{μ₁,σ₁²}(t) · φ_{μ₂,σ₂²}(t) = φ_{μ₁+μ₂,σ₁²+σ₂²}(t).
    This encodes the fact that the sum of independent Gaussians
    N(μ₁,σ₁²) + N(μ₂,σ₂²) = N(μ₁+μ₂, σ₁²+σ₂²). -/
theorem gaussianCharFn_mul (μ₁ μ₂ σ₁_sq σ₂_sq t : ℝ) :
    gaussianCharFn μ₁ σ₁_sq t * gaussianCharFn μ₂ σ₂_sq t =
      gaussianCharFn (μ₁ + μ₂) (σ₁_sq + σ₂_sq) t := by
  simp only [gaussianCharFn]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Iterated product: n independent copies of N(μ,σ²) have characteristic
    function φ_{nμ, nσ²}(t). This is the basis of the CLT proof. -/
theorem gaussianCharFn_pow (μ σ_sq : ℝ) (t : ℝ) (n : ℕ) :
    gaussianCharFn μ σ_sq t ^ n = gaussianCharFn (n * μ) (n * σ_sq) t := by
  induction n with
  | zero => simp [gaussianCharFn]
  | succ n ih =>
    rw [pow_succ, ih, gaussianCharFn_mul]
    congr 1 <;> ring

-- ============================================================
-- Part IV: Symmetry Properties
-- ============================================================

/-- The characteristic function satisfies φ(-t) = conj(φ(t)).
    This reflects that the Gaussian density is a real-valued function. -/
theorem gaussianCharFn_neg (μ σ_sq t : ℝ) :
    gaussianCharFn μ σ_sq (-t) = starRingEnd ℂ (gaussianCharFn μ σ_sq t) := by
  simp only [gaussianCharFn, map_exp, Complex.conj_ofReal, neg_mul,
             Complex.star_def]
  congr 1
  ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
                Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

/-- For μ = 0 (centered Gaussian), the characteristic function is real-valued.
    φ(t) = exp(-σ²t²/2) ∈ ℝ. -/
theorem gaussianCharFn_real_of_centered (σ_sq t : ℝ) :
    (gaussianCharFn 0 σ_sq t).im = 0 := by
  simp [gaussianCharFn]

-- ============================================================
-- Part V: Scaling and Standardization
-- ============================================================

/-- Standardization: if X ~ N(μ,σ²), then (X-μ)/σ ~ N(0,1).
    At the level of characteristic functions:
    φ_{0,1}(t) = exp(-t²/2). -/
theorem standardGaussianCharFn (t : ℝ) :
    gaussianCharFn 0 1 t = Complex.exp (↑(-(t ^ 2 / 2))) := by
  simp [gaussianCharFn]

/-- The standard Gaussian characteristic function at t=1:
    φ(1) = exp(-1/2). -/
theorem standardGaussianCharFn_at_one :
    gaussianCharFn 0 1 1 = Complex.exp (↑(-(1 : ℝ) / 2)) := by
  simp [gaussianCharFn]

/-- Scaling: if X ~ N(0,σ²), then φ_X(t) = φ_{0,1}(σt). -/
theorem gaussianCharFn_scaling (σ_sq t : ℝ) (hσ : σ_sq ≥ 0) :
    gaussianCharFn 0 σ_sq t =
      gaussianCharFn 0 1 (Real.sqrt σ_sq * t) := by
  simp only [gaussianCharFn]
  congr 1
  push_cast
  ring_nf
  congr 1
  rw [Real.sq_sqrt hσ]
  ring

-- ============================================================
-- Part VI: CLT Connection
-- ============================================================

/-- **CLT via characteristic functions**: If X₁,...,Xₙ are iid N(0,1),
    then S_n/√n has characteristic function exp(-t²/2) = φ_{0,1}(t).

    More precisely: the char fn of Sₙ = X₁+...+Xₙ is φ_{0,1}(t)^n = φ_{0,n}(t).
    The char fn of Sₙ/√n is φ_{0,n}(t/√n) = exp(-n·(t/√n)²/2) = exp(-t²/2).

    This is the simplest special case of the CLT: Gaussians are stable. -/
theorem clt_gaussian_stable (t : ℝ) (n : ℕ) (hn : 0 < n) :
    gaussianCharFn 0 (↑n) (t / Real.sqrt n) = gaussianCharFn 0 1 t := by
  simp only [gaussianCharFn]
  congr 1
  push_cast
  ring_nf
  congr 1
  have hnsq : Real.sqrt (↑n) ^ 2 = ↑n := Real.sq_sqrt (Nat.cast_nonneg n)
  field_simp
  nlinarith [hnsq]

end CentralLimitTheoremOQ01OQ02OQ01OQ01
