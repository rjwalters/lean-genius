/-
# Chebyshev's integral inequality (the continuous Chebyshev sum inequality)

The gallery entry `chebyshev-sum-inequality-oq-01-oq-01` (weighted/discrete Chebyshev)
proves the *finite* Chebyshev sum inequality with a nonnegative weight vector, and notes
that the natural next step is the **continuous (integral) Chebyshev inequality**, where the
weight becomes a measure/density.  This file supplies exactly that.

For a finite measure `μ` and two bounded measurable functions `f, g` that are *comonotone*
(similarly ordered: `(f x - f y) * (g x - g y) ≥ 0` for all `x, y`), one has

  `(∫ f) * (∫ g) ≤ μ(univ) * ∫ f·g`.

The proof is the classical comonotone (correlation) argument: the symmetric double integral
`∫∫ (f x - f y)(g x - g y) dμx dμy` is nonnegative because its integrand is, and Fubini plus
the product-integral identities expand it to `2·(μ(univ)·∫fg − (∫f)(∫g))`.

Mathlib has only the discrete `Finset` Chebyshev inequality (`Mathlib/Algebra/Order/Chebyshev.lean`);
the integral/measure-theoretic correlation inequality for comonotone functions is not present.

Boundedness keeps every integrability obligation trivial on the finite (and finite product)
measure, so the result is fully `0`-axiom verified.

Corollaries:
* `chebyshev_integral_ge_of_antitone`: the reversed inequality for oppositely ordered functions;
* `chebyshev_integral_sq`: the second-moment / Cauchy–Schwarz bound `(∫f)² ≤ μ(univ)·∫f²`;
* `chebyshev_integral_prob`: on a probability measure, `(∫f)(∫g) ≤ ∫fg` (covariance ≥ 0).
-/
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace ChebyshevSumIntegral

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A bounded measurable real function is integrable with respect to a finite measure. -/
theorem integrable_of_bounded [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (memLp_top_of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)).integrable le_top

/-- **Chebyshev's integral inequality.**  For a finite measure `μ` and bounded measurable
functions `f, g` that are *comonotone* (`(f x - f y)*(g x - g y) ≥ 0` for all `x, y`), the
average of the product dominates the product of the averages:
`(∫ f) * (∫ g) ≤ μ(univ) * ∫ f·g`. -/
theorem chebyshev_integral_mul_le [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg)
    (hmono : ∀ x y, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ μ.real Set.univ * ∫ x, f x * g x ∂μ := by
  -- integrability of the basic functions on `μ`
  have hfi : Integrable f μ := integrable_of_bounded hf hfb
  have hgi : Integrable g μ := integrable_of_bounded hg hgb
  have hfgi : Integrable (fun x => f x * g x) μ :=
    integrable_of_bounded (hf.mul hg) (C := Cf * Cg) (fun x => by
      rw [abs_mul]
      exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) (le_trans (abs_nonneg (f x)) (hfb x)))
  -- the double integral of the comonotone integrand is nonnegative
  have hnn : 0 ≤ ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) :=
    integral_nonneg (fun z => hmono z.1 z.2)
  -- the four product integrals via Fubini / the product-integral identities
  have hA : ∫ z, f z.1 * g z.1 ∂(μ.prod μ) = μ.real Set.univ * ∫ x, f x * g x ∂μ := by
    have := integral_fun_fst (μ := μ) (ν := μ) (fun x => f x * g x)
    simpa [smul_eq_mul] using this
  have hD : ∫ z, f z.2 * g z.2 ∂(μ.prod μ) = μ.real Set.univ * ∫ x, f x * g x ∂μ := by
    have := integral_fun_snd (μ := μ) (ν := μ) (fun x => f x * g x)
    simpa [smul_eq_mul] using this
  have hB : ∫ z, f z.1 * g z.2 ∂(μ.prod μ) = (∫ x, f x ∂μ) * ∫ x, g x ∂μ :=
    integral_prod_mul f g
  have hC : ∫ z, g z.1 * f z.2 ∂(μ.prod μ) = (∫ x, g x ∂μ) * ∫ x, f x ∂μ :=
    integral_prod_mul g f
  -- integrability of the four product functions on the (finite) product measure
  have hAi : Integrable (fun z : α × α => f z.1 * g z.1) (μ.prod μ) :=
    Integrable.comp_fst hfgi μ
  have hDi : Integrable (fun z : α × α => f z.2 * g z.2) (μ.prod μ) :=
    Integrable.comp_snd hfgi μ
  have hBi : Integrable (fun z : α × α => f z.1 * g z.2) (μ.prod μ) := hfi.mul_prod hgi
  have hCi : Integrable (fun z : α × α => g z.1 * f z.2) (μ.prod μ) := hgi.mul_prod hfi
  have hABi : Integrable (fun z : α × α => f z.1 * g z.1 - f z.1 * g z.2) (μ.prod μ) :=
    hAi.sub hBi
  have hABCi : Integrable
      (fun z : α × α => f z.1 * g z.1 - f z.1 * g z.2 - g z.1 * f z.2) (μ.prod μ) := hABi.sub hCi
  -- expand the double integral by linearity
  have hexp : ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ)
      = ((∫ z, f z.1 * g z.1 ∂(μ.prod μ)) - (∫ z, f z.1 * g z.2 ∂(μ.prod μ))
          - (∫ z, g z.1 * f z.2 ∂(μ.prod μ))) + (∫ z, f z.2 * g z.2 ∂(μ.prod μ)) := by
    calc ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ)
        = ∫ z, (f z.1 * g z.1 - f z.1 * g z.2 - g z.1 * f z.2 + f z.2 * g z.2) ∂(μ.prod μ) := by
          apply integral_congr_ae; filter_upwards with z; ring
      _ = ((∫ z, f z.1 * g z.1 ∂(μ.prod μ)) - (∫ z, f z.1 * g z.2 ∂(μ.prod μ))
            - (∫ z, g z.1 * f z.2 ∂(μ.prod μ))) + (∫ z, f z.2 * g z.2 ∂(μ.prod μ)) := by
          rw [integral_add hABCi hDi, integral_sub hABi hCi, integral_sub hAi hBi]
  rw [hexp, hA, hB, hC, hD] at hnn
  linarith [hnn, mul_comm (∫ x, f x ∂μ) (∫ x, g x ∂μ)]

/-- The reversed Chebyshev integral inequality for *oppositely ordered* (anti-comonotone)
functions: if `(f x - f y)*(g x - g y) ≤ 0` for all `x, y`, then
`μ(univ) * ∫ f·g ≤ (∫ f) * (∫ g)`. -/
theorem chebyshev_integral_ge_of_antitone [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg)
    (hanti : ∀ x y, (f x - f y) * (g x - g y) ≤ 0) :
    μ.real Set.univ * ∫ x, f x * g x ∂μ ≤ (∫ x, f x ∂μ) * ∫ x, g x ∂μ := by
  have hgb' : ∀ x, |-(g x)| ≤ Cg := fun x => by rw [abs_neg]; exact hgb x
  have hmono' : ∀ x y, 0 ≤ (f x - f y) * (-(g x) - -(g y)) := fun x y => by
    nlinarith [hanti x y]
  have key := chebyshev_integral_mul_le (μ := μ) hf hg.neg hfb hgb' hmono'
  simp only [mul_neg, integral_neg] at key
  nlinarith [key]

/-- Second-moment / Cauchy–Schwarz bound: a bounded measurable function always satisfies
`(∫ f)² ≤ μ(univ) * ∫ f²`.  (Comonotonicity is automatic when `g = f`.) -/
theorem chebyshev_integral_sq [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hfb : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  have h := chebyshev_integral_mul_le (μ := μ) hf hf hfb hfb (fun x y => mul_self_nonneg _)
  calc (∫ x, f x ∂μ) ^ 2 = (∫ x, f x ∂μ) * ∫ x, f x ∂μ := by ring
    _ ≤ μ.real Set.univ * ∫ x, f x * f x ∂μ := h
    _ = μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by simp_rw [← pow_two]

/-- On a probability measure, the integral Chebyshev inequality is the statement that two
comonotone (similarly ordered) random variables have nonnegative covariance:
`(∫ f) * (∫ g) ≤ ∫ f·g`. -/
theorem chebyshev_integral_prob [IsProbabilityMeasure μ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x, |f x| ≤ Cf) (hgb : ∀ x, |g x| ≤ Cg)
    (hmono : ∀ x y, 0 ≤ (f x - f y) * (g x - g y)) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have h := chebyshev_integral_mul_le (μ := μ) hf hg hfb hgb hmono
  have huniv : μ.real Set.univ = 1 := by simp [Measure.real, measure_univ]
  rw [huniv, one_mul] at h
  exact h

end ChebyshevSumIntegral
