import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-
# The anisotropic `n`-dimensional Gaussian integral: ∫_{ℝⁿ} e^{-∑ bᵢ xᵢ²} = π^{n/2} / √(∏ bᵢ)

## Open Question (area-of-circle-oq-07-oq-04-oq-01-oq-01-oq-02)
The parent `area-of-circle-oq-07-oq-04-oq-01-oq-01` proves the **isotropic** `n`-dimensional
Gaussian integral

    ∫_{ℝⁿ} e^{-b ∑ᵢ xᵢ²}  =  (π/b)^{n/2},

with a single common weight `b` on every axis.  The natural next layer is the **anisotropic**
(diagonal-covariance) Gaussian, where each coordinate `xᵢ` carries its own weight `bᵢ`:

    ∫_{ℝⁿ} e^{-∑ᵢ bᵢ xᵢ²}  =  ∏ᵢ √(π/bᵢ)  =  π^{n/2} / √(∏ᵢ bᵢ).

This is the diagonal case of the general positive-definite quadratic-form Gaussian
`∫_{ℝⁿ} e^{-⟨Ax,x⟩} = π^{n/2}/√(det A)`: for a *diagonal* matrix `A = diag(b₁,…,bₙ)` the
determinant is the product `∏ᵢ bᵢ`, and the normalising constant is `π^{n/2}/√(∏ᵢ bᵢ)`.

Here `ℝⁿ` is `Fin n → ℝ` carried by the product (Lebesgue) measure, and the integrand is the
separable product `e^{-∑ᵢ bᵢ xᵢ²} = ∏ᵢ e^{-bᵢ xᵢ²}`.

## Answer: YES.

* `gaussian_anisotropic_eq_prod` — the **product–Fubini step** (every real weight vector `b`):
  `∫_{ℝⁿ} e^{-∑ᵢ bᵢ xᵢ²} = ∏ᵢ √(π/bᵢ)`.  The separable integrand factors as the product
  `∏ᵢ e^{-bᵢ xᵢ²}` (`Real.exp_sum`); `integral_fintype_prod_volume_eq_prod` collapses the
  product integral to a *product* of line integrals (the factors now differ across axes, so we
  need the general Fubini lemma rather than the isotropic power form); each line integral is
  Mathlib's `integral_gaussian (bᵢ)`.  No positivity hypothesis: holds for every `b`.
* `gaussian_anisotropic_closed_form` — the **determinant closed form** (`bᵢ > 0`):
  `∫_{ℝⁿ} e^{-∑ᵢ bᵢ xᵢ²} = π^{n/2} / √(∏ᵢ bᵢ)`.  From the product form, `√(π/bᵢ) = √π/√bᵢ`
  factors the constant, and `∏ᵢ √bᵢ = √(∏ᵢ bᵢ)` (`Real.finset_prod_rpow`) re-assembles the
  determinant `∏ᵢ bᵢ` under a single root.
* `gaussian_isotropic_recover` — taking the constant weight vector `bᵢ = c` recovers the
  parent's isotropic closed form `(π/c)^{n/2}`, exhibiting this result as a strict generalisation.

The engine is the same separable Fubini factorisation as the isotropic parent, upgraded from a
power of one integral to a product of `n` distinct line integrals.  No new axioms.
-/

open Real MeasureTheory Finset

namespace AreaOfCircleOQ07OQ04OQ01OQ01OQ02

variable {n : ℕ}

/-- **Anisotropic product–Fubini step.** The integral of the diagonal Gaussian
`e^{-∑ᵢ bᵢ xᵢ²}` over `ℝⁿ = Fin n → ℝ` equals the product of the per-axis one-dimensional
Gaussian integrals `∏ᵢ √(π/bᵢ)`.  The separable integrand factors as `∏ᵢ e^{-bᵢ xᵢ²}`
(`Real.exp_sum`); `integral_fintype_prod_volume_eq_prod` turns the product integral into a
product of line integrals, each evaluated by Mathlib's `integral_gaussian`.  Holds for *every*
real weight vector `b` (no integrability/positivity needed). -/
theorem gaussian_anisotropic_eq_prod (b : Fin n → ℝ) :
    (∫ x : Fin n → ℝ, Real.exp (-∑ i, b i * (x i) ^ 2)) = ∏ i, Real.sqrt (π / b i) := by
  have key : (∫ x : Fin n → ℝ, ∏ i, Real.exp (-(b i) * (x i) ^ 2))
      = ∏ i, Real.sqrt (π / b i) := by
    rw [integral_fintype_prod_volume_eq_prod (fun i => fun t : ℝ => Real.exp (-(b i) * t ^ 2))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    exact integral_gaussian (b i)
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  -- beta-reduce the integrand applications `(fun x => …) x` so `Real.exp_sum` matches
  simp only []
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [neg_mul]

/-- **Determinant closed form.** For positive weights `bᵢ > 0`,
`∫_{ℝⁿ} e^{-∑ᵢ bᵢ xᵢ²} = π^{n/2} / √(∏ᵢ bᵢ)`.  This is the diagonal case of the general
quadratic-form Gaussian `π^{n/2}/√(det A)`, with `det (diag b) = ∏ᵢ bᵢ`. -/
theorem gaussian_anisotropic_closed_form (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    (∫ x : Fin n → ℝ, Real.exp (-∑ i, b i * (x i) ^ 2))
      = π ^ ((n : ℝ) / 2) / Real.sqrt (∏ i, b i) := by
  rw [gaussian_anisotropic_eq_prod]
  have hpi : (0 : ℝ) ≤ π := Real.pi_pos.le
  -- ∏ᵢ √bᵢ = √(∏ᵢ bᵢ)
  have hprod : ∏ i, Real.sqrt (b i) = Real.sqrt (∏ i, b i) := by
    simp only [Real.sqrt_eq_rpow]
    exact Real.finset_prod_rpow Finset.univ b (fun i _ => (hb i).le) (1 / 2)
  -- (√π)ⁿ = π^{n/2}
  have hsq : (Real.sqrt π) ^ n = π ^ ((n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (π ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul hpi]
    congr 1
    ring
  calc ∏ i, Real.sqrt (π / b i)
      = ∏ i, Real.sqrt π / Real.sqrt (b i) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [Real.sqrt_div hpi]
    _ = (∏ i : Fin n, Real.sqrt π) / ∏ i, Real.sqrt (b i) := by rw [Finset.prod_div_distrib]
    _ = (Real.sqrt π) ^ n / Real.sqrt (∏ i, b i) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hprod]
    _ = π ^ ((n : ℝ) / 2) / Real.sqrt (∏ i, b i) := by rw [hsq]

/-- **Isotropic recovery.** Taking the constant weight vector `bᵢ = c` (with `c > 0`) recovers
the parent's isotropic `n`-dimensional Gaussian closed form `(π/c)^{n/2}`, so this anisotropic
statement is a strict generalisation of `area-of-circle-oq-07-oq-04-oq-01-oq-01`. -/
theorem gaussian_isotropic_recover (c : ℝ) (hc : 0 < c) (n : ℕ) :
    (∫ x : Fin n → ℝ, Real.exp (-∑ i, c * (x i) ^ 2)) = (π / c) ^ ((n : ℝ) / 2) := by
  -- the constant weight vector collapses the product to a power of the single line integral
  have h : (∫ x : Fin n → ℝ, Real.exp (-∑ i, c * (x i) ^ 2))
      = ∏ _i : Fin n, Real.sqrt (π / c) := gaussian_anisotropic_eq_prod (fun _ => c)
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpc : (0 : ℝ) ≤ π / c := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((π / c) ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul hpc]
  congr 1
  ring

end AreaOfCircleOQ07OQ04OQ01OQ01OQ02
