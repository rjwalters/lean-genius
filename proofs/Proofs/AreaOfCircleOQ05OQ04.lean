/-
Area of Circle OQ-05-OQ-04 (S2a + S3 + S4a + S5): The Complex Gaussian Integral

Proves the complex Gaussian identities

    ∫_ℂ exp(-π · ‖z‖²) dz = 1                       (S2a, b = π specialisation)
    ∫_ℂ exp(-(b · ‖z‖²)) dz = π / b                 (S3, parametric in b > 0)
    ∫_{ℂⁿ} exp(-(b · ∑ ‖zᵢ‖²)) dz = (π/b)ⁿ          (S4a, n-dim parametric)
    ∫_ℂ exp(-(b · ‖z - c‖²)) dz = π / b             (S5, translation invariant)

and the natural corollaries `∫_ℂ exp(-‖z‖²) dz = π` (unit weight,
"complex Gaussian = area of unit disc"), the probability density
`∫_ℂ (1/π) · exp(-‖z‖²) dz = 1`, the multidimensional analogues
`∫_{ℂⁿ} exp(-∑ ‖zᵢ‖²) = πⁿ` and `∫_{ℂⁿ} (1/π)ⁿ · exp(-∑‖zᵢ‖²) = 1`, and
the shifted probability density `∫_ℂ (b/π) · exp(-(b · ‖z - c‖²)) dz = 1`
(canonical two-parameter complex Gaussian, mean `c`, scale `b`).

The S2a results assert that the Gaussian density `e^{-π |z|²}` on ℂ
integrates to 1 against the standard Lebesgue measure on ℂ (induced
by the canonical identification ℂ ≃ ℝ²). The S3 additions generalise
to arbitrary positive weights, completing the complex analogue of the
parent file's scalar `scaled_gaussian` (`∫ exp(-(a · x²)) = √(π/a)`).

## Context (from `research/area-of-circle-oq-05-oq-04/problem.md`)

The OQ source formula

    ∫_{ℚ_p} e^{2πi ‖x‖_p} dx = 1

is malformed for genuine p-adic reasons (the norm `‖·‖_p` is real-valued;
the integrand carries no p-adic information; and Haar measure on ℚ_p is
infinite). The S1 OBSERVE pass identified three well-defined repair targets:

  * (C1) `∫_{ℤ_p} ψ_p dμ = 1` — trivial.
  * (C2) `𝟙_{ℤ_p}` is self-Fourier under `(ψ_p, Haar μ(ℤ_p)=1)` — the
         intended p-adic Gaussian analogue; needs Mathlib infrastructure
         not yet upstreamed (standard additive character `ψ_p : ℚ_p → ℂ`,
         explicit `MeasureTheory.Measure ℚ_p`).
  * (C3) Tate / Igusa local zeta — far heavier.

The OQ source also references the case "over ℂ", which is the immediate
follow-on this file delivers. This is the "S2a safe bridge" recommendation
of `research/area-of-circle-oq-05-oq-04/state.md`: ~50 lines, 0 sorries,
0 axioms, downstream of existing Mathlib + parent infrastructure.

## Proof Strategy

The complex Gaussian reduces to a product of two real Gaussians via the
measure-preserving identification ℂ ≃ ℝ × ℝ:

1. Mathlib's `Complex.volume_preserving_equiv_real_prod` exhibits the
   `MeasurableEquiv` `ℂ ≃ᵐ ℝ × ℝ`, `z ↦ (z.re, z.im)`, as a
   measure-preserving map between `(volume : Measure ℂ)` and the product
   measure on `ℝ × ℝ`.

2. Pulling the integrand back via `MeasurePreserving.integral_comp'`,
   `∫_ℂ exp(-π · normSq z) dz = ∫_{ℝ × ℝ} exp(-π · (x² + y²)) d(x,y)`.

3. Factor the integrand: `exp(-π · (x² + y²)) = exp(-π x²) · exp(-π y²)`
   (`Real.exp_add` after `mul_add` and `neg_add`).

4. `MeasureTheory.volume_eq_prod` rewrites the volume on `ℝ × ℝ` as
   `volume.prod volume`, after which `integral_prod_mul` factors the
   double integral into a product of single integrals.

5. Each single-variable factor is `∫ exp(-π · x²) dx = √(π/π) = 1`
   by the parent file's `scaled_gaussian` at `a = π`.

The whole proof is sorry-free and axiom-free.

## Why this case but not the p-adic case

The p-adic case (C2) is a multi-session attack that requires *first*
contributing the missing Mathlib infrastructure (standard ψ_p and Haar
on ℚ_p, two distinct upstream PRs). The complex case is essentially a
2-line corollary of `integral_gaussian` plus Fubini, which is the
appropriate single-session deliverable for tier-B / S2a.

Parent: `AreaOfCircleOQ05OQ02.lean` (multivariate Gaussian, all proved).
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Proofs.AreaOfCircleOQ05

namespace ComplexGaussianCircle

open MeasureTheory MeasureTheory.Measure Real Complex
open scoped FourierTransform RealInnerProductSpace

/-- The scalar π-weighted Gaussian integral: ∫ exp(-(π · x²)) dx = 1.

Direct consequence of the parent file's `scaled_gaussian` with `a = π`:
`∫ exp(-(π · x²)) = √(π / π) = √1 = 1`. -/
theorem integral_pi_gaussian :
    ∫ x : ℝ, Real.exp (-(Real.pi * x ^ 2)) = 1 := by
  have h := GaussianIntegralCircle.scaled_gaussian Real.pi Real.pi_pos
  rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one] at h
  exact h

/-- Helper: the integrand factors as a product under the `ℂ ≃ᵐ ℝ × ℝ`
identification.

For `p : ℝ × ℝ`, `exp(-(π · (p.1² + p.2²))) = exp(-(π · p.1²)) · exp(-(π · p.2²))`. -/
private lemma exp_factor (p : ℝ × ℝ) :
    Real.exp (-(Real.pi * (p.1 ^ 2 + p.2 ^ 2))) =
      Real.exp (-(Real.pi * p.1 ^ 2)) * Real.exp (-(Real.pi * p.2 ^ 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The complex Gaussian integral over ℂ with `b = π`:

    ∫_ℂ exp(-π · ‖z‖²) dz = 1.

Equivalent formulation (via `normSq_eq_norm_sq`): the Gaussian density
`exp(-π · normSq z)` integrates to 1 against the canonical Lebesgue
measure on ℂ. This is the "bonus complex case" from
`problem.md` §"Complex case (over ℂ)" — the well-defined sibling of
the malformed p-adic source formula.

Proof: pull back along `Complex.measurableEquivRealProd` (measure-preserving),
factor the integrand via `exp_factor`, and apply Fubini
(`integral_prod_mul`) to get a product of two scalar π-Gaussians, each
equal to 1 by `integral_pi_gaussian`. -/
theorem complex_gaussian_integral :
    ∫ z : ℂ, Real.exp (-(Real.pi * Complex.normSq z)) = 1 := by
  -- Step 1: rewrite the integrand to expose (z.re, z.im) on ℂ side, since
  -- `normSq z = z.re * z.re + z.im * z.im` matches `p.1^2 + p.2^2` after
  -- `mul_self = sq`.
  have h_re_im : ∀ z : ℂ,
      Real.exp (-(Real.pi * Complex.normSq z)) =
        Real.exp (-(Real.pi * (z.re ^ 2 + z.im ^ 2))) := by
    intro z
    congr 2
    rw [Complex.normSq_apply, sq, sq]
  simp_rw [h_re_im]
  -- Step 2: transport ∫_ℂ to ∫_{ℝ × ℝ} via measurableEquivRealProd.
  -- The function `g : ℝ × ℝ → ℝ` is `fun p => exp(-(π * (p.1^2 + p.2^2)))`.
  -- Under the equivalence, `(measurableEquivRealProd z).1 = z.re` and
  -- `(measurableEquivRealProd z).2 = z.im`, so we can rewrite the LHS as
  -- `∫ z, g(measurableEquivRealProd z)`.
  have h_pull :
      ∫ z : ℂ, Real.exp (-(Real.pi * (z.re ^ 2 + z.im ^ 2))) =
        ∫ p : ℝ × ℝ, Real.exp (-(Real.pi * (p.1 ^ 2 + p.2 ^ 2))) := by
    have := Complex.volume_preserving_equiv_real_prod.integral_comp'
      (g := fun p : ℝ × ℝ => Real.exp (-(Real.pi * (p.1 ^ 2 + p.2 ^ 2))))
    -- `this : ∫ z, g (measurableEquivRealProd z) = ∫ p, g p`
    -- and `measurableEquivRealProd_apply z = (z.re, z.im)`.
    simpa using this
  rw [h_pull]
  -- Step 3: factor the integrand into a product, then apply Fubini.
  simp_rw [exp_factor]
  -- Step 4: `(volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ)`
  -- is `rfl` (`MeasureTheory.Measure.volume_eq_prod`), so `integral_prod_mul`
  -- applies after a `volume_eq_prod` rewrite.
  rw [volume_eq_prod ℝ ℝ, integral_prod_mul (μ := volume) (ν := volume)
      (fun x => Real.exp (-(Real.pi * x ^ 2)))
      (fun y => Real.exp (-(Real.pi * y ^ 2)))]
  -- Step 5: each factor is 1 by `integral_pi_gaussian`; product `1 * 1 = 1`.
  simp_rw [integral_pi_gaussian]
  norm_num

/-- Restated in terms of `‖z‖²` (preferred for downstream use): the
Gaussian density `exp(-π · ‖z‖²)` on ℂ integrates to 1.

This is `complex_gaussian_integral` with the integrand expressed via
the analytic norm `‖z‖` instead of `Complex.normSq z`. The two forms are
equivalent by `Complex.normSq_eq_norm_sq : normSq z = ‖z‖²`. -/
theorem complex_gaussian_integral_norm :
    ∫ z : ℂ, Real.exp (-(Real.pi * ‖z‖ ^ 2)) = 1 := by
  have h_eq : ∀ z : ℂ,
      Real.exp (-(Real.pi * ‖z‖ ^ 2)) =
        Real.exp (-(Real.pi * Complex.normSq z)) := by
    intro z
    rw [Complex.normSq_eq_norm_sq]
  simp_rw [h_eq]
  exact complex_gaussian_integral

/-! ## Part 2: Parametric complex Gaussian (S3)

The S2a deliverable specialised the integrand to `b = π`. The natural
strict generalisation is parametric in `b > 0`:

    ∫_ℂ exp(-(b · normSq z)) dz = π / b.

This is the complex analogue of the parent file's `scaled_gaussian`
(`∫ exp(-(a · x²)) dx = √(π/a)`): the complex-plane factor is
`(√(π/b))² = π/b`. The earlier theorem `complex_gaussian_integral`
becomes the special case `b = π`, with `π / π = 1`. -/

/-- The general `b`-scaled scalar Gaussian: `∫ exp(-(b · x²)) = √(π/b)`.

This is simply a re-export of `GaussianIntegralCircle.scaled_gaussian`
to live in the same namespace as the complex variants below, so that
all `b`-parametric Gaussians sit side-by-side. -/
theorem integral_b_gaussian (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, Real.exp (-(b * x ^ 2)) = √(Real.pi / b) :=
  GaussianIntegralCircle.scaled_gaussian b hb

/-- Helper: the integrand factors as a product under the `ℂ ≃ᵐ ℝ × ℝ`
identification, with a general weight `b`.

For `p : ℝ × ℝ`, `exp(-(b · (p.1² + p.2²))) = exp(-(b · p.1²)) · exp(-(b · p.2²))`.
This is the `b`-parameterised counterpart of `exp_factor`. -/
private lemma exp_factor_b (b : ℝ) (p : ℝ × ℝ) :
    Real.exp (-(b * (p.1 ^ 2 + p.2 ^ 2))) =
      Real.exp (-(b * p.1 ^ 2)) * Real.exp (-(b * p.2 ^ 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Parametric complex Gaussian integral**: for any `b > 0`,

    ∫_ℂ exp(-(b · normSq z)) dz = π / b.

This is the strict generalisation of `complex_gaussian_integral`
(`b = π`) and the complex analogue of `scaled_gaussian` (`√(π/b)` per
axis, squared by Fubini to `π / b`).

Proof: same skeleton as `complex_gaussian_integral` — pull back along
`Complex.measurableEquivRealProd`, factor the integrand via
`exp_factor_b`, apply Fubini (`integral_prod_mul`), and combine the
two scalar factors `√(π/b) · √(π/b) = π/b` via `Real.mul_self_sqrt`. -/
theorem complex_gaussian_integral_scaled (b : ℝ) (hb : 0 < b) :
    ∫ z : ℂ, Real.exp (-(b * Complex.normSq z)) = Real.pi / b := by
  -- Step 1: rewrite `normSq z` as `z.re² + z.im²` to expose product structure.
  have h_re_im : ∀ z : ℂ,
      Real.exp (-(b * Complex.normSq z)) =
        Real.exp (-(b * (z.re ^ 2 + z.im ^ 2))) := by
    intro z
    congr 2
    rw [Complex.normSq_apply, sq, sq]
  simp_rw [h_re_im]
  -- Step 2: transport ∫_ℂ to ∫_{ℝ × ℝ} via measurableEquivRealProd.
  have h_pull :
      ∫ z : ℂ, Real.exp (-(b * (z.re ^ 2 + z.im ^ 2))) =
        ∫ p : ℝ × ℝ, Real.exp (-(b * (p.1 ^ 2 + p.2 ^ 2))) := by
    have := Complex.volume_preserving_equiv_real_prod.integral_comp'
      (g := fun p : ℝ × ℝ => Real.exp (-(b * (p.1 ^ 2 + p.2 ^ 2))))
    simpa using this
  rw [h_pull]
  -- Step 3: factor the integrand into a product.
  simp_rw [exp_factor_b b]
  -- Step 4: Fubini.
  rw [volume_eq_prod ℝ ℝ, integral_prod_mul (μ := volume) (ν := volume)
      (fun x => Real.exp (-(b * x ^ 2)))
      (fun y => Real.exp (-(b * y ^ 2)))]
  -- Step 5: each factor is √(π/b); the product is π/b.
  simp_rw [integral_b_gaussian b hb]
  -- √(π/b) * √(π/b) = π/b for π/b ≥ 0.
  exact Real.mul_self_sqrt (div_nonneg Real.pi_nonneg hb.le)

/-- `‖z‖²` form of `complex_gaussian_integral_scaled`:

    ∫_ℂ exp(-(b · ‖z‖²)) dz = π / b.

Useful for downstream consumers that prefer the analytic norm to
`Complex.normSq`. -/
theorem complex_gaussian_integral_scaled_norm (b : ℝ) (hb : 0 < b) :
    ∫ z : ℂ, Real.exp (-(b * ‖z‖ ^ 2)) = Real.pi / b := by
  have h_eq : ∀ z : ℂ,
      Real.exp (-(b * ‖z‖ ^ 2)) = Real.exp (-(b * Complex.normSq z)) := by
    intro z
    rw [Complex.normSq_eq_norm_sq]
  simp_rw [h_eq]
  exact complex_gaussian_integral_scaled b hb

/-- **Standard complex Gaussian (unit weight)**: `∫_ℂ exp(-‖z‖²) dz = π`.

    The unit-weight complex Gaussian integrates exactly to π — the area
    of the unit disc on `ℂ`. This is the canonical statement linking
    the complex Gaussian to the "circle area" theme of the slug:
    the Gaussian density `exp(-‖z‖²)` has total mass π, exactly the
    area enclosed by the unit circle. -/
theorem complex_gaussian_integral_unit_norm :
    ∫ z : ℂ, Real.exp (-‖z‖ ^ 2) = Real.pi := by
  have h := complex_gaussian_integral_scaled_norm 1 one_pos
  -- `h : ∫ z, exp(-(1 * ‖z‖^2)) = π / 1`; simp normalises `1 * x = x` and `π / 1 = π`.
  simp only [one_mul, div_one] at h
  exact h

/-- **Normalised complex Gaussian density**: the complex-plane density
    `(1/π) · exp(-‖z‖²)` integrates to 1.

    This is the complex analogue of the parent file's standard normal
    normalisation `∫ (1/√(2π)) · exp(-x²/2) dx = 1`
    (`GaussianIntegralCircle.standard_normal_normalization`). It says
    that the unit-weight complex Gaussian, divided by π, is a
    probability density on ℂ. -/
theorem complex_gaussian_integral_normalised :
    ∫ z : ℂ, (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) = 1 := by
  rw [integral_const_mul, complex_gaussian_integral_unit_norm, one_div,
      inv_mul_cancel₀ Real.pi_ne_zero]

/-! ## Part 3: The n-dimensional complex Gaussian (S4a)

The parametric complex Gaussian generalises uniformly in dimension: for
`n : ℕ` and `b > 0`,

    ∫_{ℂⁿ} exp(-(b · ∑ᵢ ‖zᵢ‖²)) dz = (π / b)ⁿ.

This is the complex-side counterpart of the parent file's diagonal real
Gaussian (`AreaOfCircleOQ05OQ02.diagonal_gaussian`, with a uniform weight
`b`): each ℂ-axis contributes a factor `π/b` (via
`complex_gaussian_integral_scaled_norm`), and `n` axes compose by
`integral_fintype_prod_volume_eq_pow`. The proof skeleton mirrors
`diagonal_gaussian` (`← Finset.sum_neg_distrib` + `Real.exp_sum` +
n-fold Fubini), differing only in that the per-axis factor is itself the
2-real-dimensional `complex_gaussian_integral_scaled_norm` rather than
the 1-real-dimensional `scaled_gaussian`. -/

/-- **n-dimensional parametric complex Gaussian**: for `b > 0` and `n : ℕ`,

    ∫_{ℂⁿ} exp(-(b · ∑ᵢ ‖zᵢ‖²)) dz = (π / b)ⁿ.

The `n = 1` case is `complex_gaussian_integral_scaled_norm` after the
trivial reindexing `Fin 1 → ℂ ≃ ℂ`. The `n = 2` case is the joint
density used in the 2-mode coherent-state model in quantum optics
(each mode contributes `π/b`).

Proof: factor the exponential of a sum as a product (`Real.exp_sum`),
apply n-fold Fubini (`integral_fintype_prod_volume_eq_pow`), and
evaluate each ℂ-factor by `complex_gaussian_integral_scaled_norm`. -/
theorem complex_gaussian_integral_scaled_pow {n : ℕ} (b : ℝ) (hb : 0 < b) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, ‖z i‖ ^ 2)) = (Real.pi / b) ^ n := by
  -- Step 1: factor exp(-(b · ∑ᵢ ‖zᵢ‖²)) = ∏ᵢ exp(-(b · ‖zᵢ‖²)).
  -- Distribute `b` into the sum, then push the negation inside, then
  -- apply `Real.exp_sum`. This is the same pattern as the parent file's
  -- `diagonal_gaussian` (real-axis n-fold Gaussian).
  simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  -- Step 2: n-fold Fubini over `Fin n → ℂ`. The integrand `∏ᵢ exp(-(b · ‖z i‖²))`
  -- has the shape `∏ᵢ f (z i)` with `f := fun z : ℂ => exp(-(b · ‖z‖²))`,
  -- so `integral_fintype_prod_volume_eq_pow` applies and gives
  -- `(∫ z : ℂ, f z) ^ Fintype.card (Fin n)`.
  rw [integral_fintype_prod_volume_eq_pow
        (ι := Fin n) (fun z : ℂ => Real.exp (-(b * ‖z‖ ^ 2)))]
  -- Step 3: evaluate the per-axis factor (`π/b`) and collapse `Fintype.card (Fin n) = n`.
  rw [complex_gaussian_integral_scaled_norm b hb, Fintype.card_fin]

/-- `normSq` form of the n-dimensional parametric complex Gaussian:

    ∫_{ℂⁿ} exp(-(b · ∑ᵢ normSq (zᵢ))) dz = (π / b)ⁿ.

This is the version that pairs directly with the `Complex.normSq` form
of the `n = 1` theorem `complex_gaussian_integral_scaled`. Useful for
consumers that prefer the algebraic `normSq` to the analytic `‖·‖²`. -/
theorem complex_gaussian_integral_scaled_pow_normSq {n : ℕ} (b : ℝ) (hb : 0 < b) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, Complex.normSq (z i))) = (Real.pi / b) ^ n := by
  -- Replace each `normSq (z i)` by `‖z i‖ ^ 2` inside the sum, then reduce to
  -- the `‖·‖²` version. Using `simp_rw` (rather than `congr`) keeps the
  -- additive-monoid structure on the sum's codomain fully determined.
  simp_rw [Complex.normSq_eq_norm_sq]
  exact complex_gaussian_integral_scaled_pow b hb

/-- **n-dimensional unit-weight complex Gaussian**: ∫_{ℂⁿ} exp(-∑ᵢ ‖zᵢ‖²) dz = πⁿ.

The unit-weight case `b = 1` of `complex_gaussian_integral_scaled_pow`.
Generalises `complex_gaussian_integral_unit_norm` (the `n = 1` value `π`)
to arbitrary dimension. -/
theorem complex_gaussian_integral_pow_unit_norm {n : ℕ} :
    ∫ z : Fin n → ℂ, Real.exp (-∑ i, ‖z i‖ ^ 2) = Real.pi ^ n := by
  have h := complex_gaussian_integral_scaled_pow (n := n) 1 one_pos
  -- `h : ∫ z, exp(-(1 * ∑ᵢ ‖zᵢ‖²)) = (π / 1) ^ n`.
  simp only [one_mul, div_one] at h
  exact h

/-- **Normalised n-dimensional complex Gaussian density**: the
    n-dimensional unit-weight Gaussian divided by `πⁿ` is a probability
    density on `ℂⁿ`:

    ∫_{ℂⁿ} (1/π)ⁿ · exp(-∑ᵢ ‖zᵢ‖²) dz = 1.

This is the multidimensional analogue of
`complex_gaussian_integral_normalised`. -/
theorem complex_gaussian_integral_pow_normalised {n : ℕ} :
    ∫ z : Fin n → ℂ, (1 / Real.pi) ^ n * Real.exp (-∑ i, ‖z i‖ ^ 2) = 1 := by
  rw [integral_const_mul, complex_gaussian_integral_pow_unit_norm,
      one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero n Real.pi_ne_zero)]

/-! ## Part 4: Translation invariance and the shifted Gaussian density (S5)

The complex Lebesgue measure is an additive Haar measure, hence invariant
under translation `z ↦ z + c`. Composing this with the parametric complex
Gaussian (S3, `complex_gaussian_integral_scaled_norm`) yields the
**shifted** complex Gaussian identity

    ∫_ℂ exp(-(b · ‖z - c‖²)) dz = π / b              (for any `c : ℂ`, `b > 0`)

and, after dividing by `π/b`, the canonical two-parameter probability
density on `ℂ` with mean `c` and scale `b`,

    ∫_ℂ (b/π) · exp(-(b · ‖z - c‖²)) dz = 1.

This is the complex analogue of the real one-dimensional Gaussian density
`(a/π)^{1/2} · exp(-(a · (x-μ)²))` familiar from probability theory; in
information-theoretic terms (cf. `ShannonEntropyOQ01.lean`) it is the
*translation-invariance* property used to show that the differential
entropy of a complex Gaussian depends only on the scale `b`, not on the
mean `c`.

The proof reduces to `complex_gaussian_integral_scaled_norm` via
`MeasureTheory.integral_add_right_eq_self`, applied to the volume
measure on `ℂ` (which is `IsAddRightInvariant` as an additive Haar
measure). The mechanism is identical to the real-line translation
invariance used in `ShannonEntropyOQ01.differential_entropy_translation_invariant`
and `FourierSeriesOQ02.lean`'s Fourier-coefficient shift lemma. -/

/-- **Translation invariance of the parametric complex Gaussian**: for
any shift `c : ℂ` and weight `b > 0`,

    ∫_ℂ exp(-(b · ‖z - c‖²)) dz = π / b.

The `c = 0` case is `complex_gaussian_integral_scaled_norm`. The proof
applies translation invariance of the complex Lebesgue (= additive Haar)
measure: writing `z - c = z + (-c)`, the substitution `w = z + (-c)`
preserves the volume, so the integral coincides with the unshifted
parametric complex Gaussian.

Proof skeleton (matching the real-line pattern in
`ShannonEntropyOQ01.differential_entropy_translation_invariant`):
rewrite the integrand `exp(-(b · ‖z - c‖²))` as the value at `z + (-c)`
of the function `w ↦ exp(-(b · ‖w‖²))`, then apply
`MeasureTheory.integral_add_right_eq_self`. -/
theorem complex_gaussian_integral_scaled_shifted_norm (b : ℝ) (hb : 0 < b) (c : ℂ) :
    ∫ z : ℂ, Real.exp (-(b * ‖z - c‖ ^ 2)) = Real.pi / b := by
  -- Step 1: rewrite the integrand into the shape `(fun w ↦ exp(-(b · ‖w‖²))) (z + (-c))`
  -- using `sub_eq_add_neg`. The β-reduction `(fun w ↦ f w) (z + (-c)) = f (z + (-c))`
  -- is definitional, so the per-point equality is just a `rw [sub_eq_add_neg]`
  -- after exposing the pre-β form via a `show`. This matches the idiom used in
  -- `ShannonEntropyOQ01.gaussian_variance` for the same translation-invariance step.
  have key : ∀ z : ℂ,
      (fun w : ℂ => Real.exp (-(b * ‖w‖ ^ 2))) (z + (-c)) =
        Real.exp (-(b * ‖z - c‖ ^ 2)) := by
    intro z
    show Real.exp (-(b * ‖z + (-c)‖ ^ 2)) = Real.exp (-(b * ‖z - c‖ ^ 2))
    rw [← sub_eq_add_neg]
  rw [show (fun z : ℂ => Real.exp (-(b * ‖z - c‖ ^ 2))) =
          (fun z : ℂ => (fun w : ℂ => Real.exp (-(b * ‖w‖ ^ 2))) (z + (-c))) from
        funext (fun z => (key z).symm)]
  -- Step 2: chain translation invariance of `volume : Measure ℂ` (an
  -- `IsAddHaarMeasure`, hence `IsAddRightInvariant`) with the unshifted
  -- parametric complex Gaussian.
  exact (integral_add_right_eq_self (fun w : ℂ => Real.exp (-(b * ‖w‖ ^ 2))) (-c)).trans
    (complex_gaussian_integral_scaled_norm b hb)

/-- **Translation invariance of the parametric complex Gaussian (`normSq` form)**:
for any shift `c : ℂ` and `b > 0`,

    ∫_ℂ exp(-(b · normSq (z - c))) dz = π / b.

This is the algebraic `Complex.normSq` companion of
`complex_gaussian_integral_scaled_shifted_norm`. -/
theorem complex_gaussian_integral_scaled_shifted (b : ℝ) (hb : 0 < b) (c : ℂ) :
    ∫ z : ℂ, Real.exp (-(b * Complex.normSq (z - c))) = Real.pi / b := by
  simp_rw [Complex.normSq_eq_norm_sq]
  exact complex_gaussian_integral_scaled_shifted_norm b hb c

/-- **Unit-weight shifted complex Gaussian**: for any shift `c : ℂ`,

    ∫_ℂ exp(-‖z - c‖²) dz = π.

The shifted form of `complex_gaussian_integral_unit_norm`, capturing the
fact that the total mass of `exp(-‖z - c‖²)` is exactly the area of the
unit disc, independent of where the Gaussian is centred. -/
theorem complex_gaussian_integral_unit_shifted_norm (c : ℂ) :
    ∫ z : ℂ, Real.exp (-‖z - c‖ ^ 2) = Real.pi := by
  have h := complex_gaussian_integral_scaled_shifted_norm 1 one_pos c
  -- `h : ∫ z, exp(-(1 * ‖z - c‖²)) = π / 1`. Normalise `1 * x = x` and `π / 1 = π`.
  simp only [one_mul, div_one] at h
  exact h

/-- **Shifted complex Gaussian probability density** (mean `c`, scale `b`):
for any `c : ℂ` and `b > 0`,

    ∫_ℂ (b / π) · exp(-(b · ‖z - c‖²)) dz = 1.

This is the canonical two-parameter complex Gaussian density on `ℂ`. The
`c = 0` case is `complex_gaussian_integral_scaled` after multiplying by
`b/π`; the `b = 1` case specialises to
`(1/π) · exp(-‖z - c‖²)`, the shifted analogue of
`complex_gaussian_integral_normalised`.

Proof: pull the constant `b/π` outside the integral
(`integral_const_mul`), apply the shifted parametric integral
(`complex_gaussian_integral_scaled_shifted_norm`), then simplify
`(b/π) · (π/b) = 1` via `field_simp`. -/
theorem complex_gaussian_density_shifted (b : ℝ) (hb : 0 < b) (c : ℂ) :
    ∫ z : ℂ, (b / Real.pi) * Real.exp (-(b * ‖z - c‖ ^ 2)) = 1 := by
  rw [integral_const_mul, complex_gaussian_integral_scaled_shifted_norm b hb c]
  field_simp

/-! ## Part 5: Translation invariance in n dimensions (S6a)

Lifting S5 (translation invariance on `ℂ`) to `Fin n → ℂ` yields the
n-dimensional shifted complex Gaussian

    ∫_{ℂⁿ} exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = (π/b)ⁿ      (for any c : Fin n → ℂ)

and the corresponding probability density

    ∫_{ℂⁿ} (b/π)ⁿ · exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = 1.

The proof mirrors S4a (n-dim, unshifted) modulo the choice of Fubini
lemma. S4a used `integral_fintype_prod_volume_eq_pow` because the
per-axis factor `z ↦ exp(-(b · ‖z‖²))` was uniform in the index `i`.
Here the per-axis factor `z ↦ exp(-(b · ‖z - cᵢ‖²))` depends on `i`
through the shift `cᵢ`, so we use the heterogeneous variant
`integral_fintype_prod_volume_eq_prod`. After Fubini, each per-axis
integral evaluates to `π/b` via S5 (translation invariance on `ℂ`;
specifically `complex_gaussian_integral_scaled_shifted_norm`),
yielding `∏ i : Fin n, (π/b) = (π/b)ⁿ` by `Finset.prod_const`.

See `research/area-of-circle-oq-05-oq-04/s6a-prep-pi-haar-vs-fubini.md`
for the rejected pi-Haar route (Path A) and the rationale for the
Fubini route (Path B) used here. -/

/-- **n-dimensional shifted parametric complex Gaussian**: for `b > 0`,
`n : ℕ`, and any shift vector `c : Fin n → ℂ`,

    ∫_{ℂⁿ} exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = (π / b)ⁿ.

Strictly generalises `complex_gaussian_integral_scaled_pow` (S4a,
`c = 0` case) and `complex_gaussian_integral_scaled_shifted_norm`
(S5, `n = 1` case). The proof mirrors S4a's `_pow` proof but uses
the heterogeneous Fubini variant `integral_fintype_prod_volume_eq_prod`
(per-axis factor depends on `i` via `cᵢ`), followed by an S5 collapse
of each per-axis integral to `π/b` (independent of `cᵢ`). -/
theorem complex_gaussian_integral_scaled_pow_shifted_norm
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = (Real.pi / b) ^ n := by
  -- Step 1: factor exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = ∏ᵢ exp(-(b · ‖zᵢ - cᵢ‖²)).
  -- Same first move as S4a (line 332), with the per-axis squared norm
  -- now `‖z i - c i‖²` rather than `‖z i‖²`.
  simp_rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  -- Step 2: heterogeneous n-fold Fubini. The integrand
  -- `∏ᵢ exp(-(b · ‖z i - c i‖²))` has the shape `∏ᵢ f i (z i)` with
  -- `f i z = exp(-(b · ‖z - c i‖²))`, depending on `i` through `c i`.
  -- So we use `integral_fintype_prod_volume_eq_prod` (heterogeneous)
  -- rather than `_eq_pow` (uniform); see `s6a-prep-pi-haar-vs-fubini.md`.
  rw [integral_fintype_prod_volume_eq_prod
        (fun (i : Fin n) (z : ℂ) => Real.exp (-(b * ‖z - c i‖ ^ 2)))]
  -- Step 3: each per-axis integral evaluates to `π/b` via S5
  -- (the value does not depend on the shift `c i`, only the integrand does).
  simp_rw [complex_gaussian_integral_scaled_shifted_norm b hb]
  -- Step 4: collapse the constant product `∏ i : Fin n, (π/b) = (π/b)^n`.
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- `normSq` form of the n-dimensional shifted parametric complex Gaussian:

    ∫_{ℂⁿ} exp(-(b · ∑ᵢ normSq (zᵢ - cᵢ))) dz = (π / b)ⁿ.

Companion form of `complex_gaussian_integral_scaled_pow_shifted_norm`
expressed via `Complex.normSq` rather than the analytic `‖·‖²`.
Mirror of `complex_gaussian_integral_scaled_pow_normSq` at line 349. -/
theorem complex_gaussian_integral_scaled_pow_shifted_normSq
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-(b * ∑ i, Complex.normSq (z i - c i))) =
      (Real.pi / b) ^ n := by
  simp_rw [Complex.normSq_eq_norm_sq]
  exact complex_gaussian_integral_scaled_pow_shifted_norm b hb c

/-- **n-dimensional unit-weight shifted complex Gaussian**: for any
`n : ℕ` and any shift `c : Fin n → ℂ`,

    ∫_{ℂⁿ} exp(-∑ᵢ ‖zᵢ - cᵢ‖²) dz = πⁿ.

The unit-weight `b = 1` case of
`complex_gaussian_integral_scaled_pow_shifted_norm`, generalising the
`c = 0` n-dim corollary `complex_gaussian_integral_pow_unit_norm` and
the `n = 1` shifted corollary `complex_gaussian_integral_unit_shifted_norm`. -/
theorem complex_gaussian_integral_pow_unit_shifted_norm
    {n : ℕ} (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, Real.exp (-∑ i, ‖z i - c i‖ ^ 2) = Real.pi ^ n := by
  have h := complex_gaussian_integral_scaled_pow_shifted_norm (n := n) 1 one_pos c
  simp only [one_mul, div_one] at h
  exact h

/-- **Shifted n-dimensional complex Gaussian probability density**
(mean `c : Fin n → ℂ`, scale `b > 0`): for any `n : ℕ`,

    ∫_{ℂⁿ} (b/π)ⁿ · exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = 1.

The canonical two-parameter complex Gaussian probability density on
`ℂⁿ`, strictly generalising `complex_gaussian_integral_pow_normalised`
(`c = 0` case) and `complex_gaussian_density_shifted` (`n = 1` case).

Proof: pull `(b/π)ⁿ` outside the integral via `integral_const_mul`,
apply `complex_gaussian_integral_scaled_pow_shifted_norm` to evaluate
the integral to `(π/b)ⁿ`, then collapse `(b/π)ⁿ · (π/b)ⁿ = 1` via
`← mul_pow` and `field_simp`. -/
theorem complex_gaussian_density_pow_shifted
    {n : ℕ} (b : ℝ) (hb : 0 < b) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, (b / Real.pi) ^ n *
      Real.exp (-(b * ∑ i, ‖z i - c i‖ ^ 2)) = 1 := by
  rw [integral_const_mul, complex_gaussian_integral_scaled_pow_shifted_norm b hb c,
      ← mul_pow]
  have h : (b / Real.pi) * (Real.pi / b) = 1 := by
    have hb' : b ≠ 0 := ne_of_gt hb
    field_simp
  rw [h, one_pow]

/-! ## Part 6: Complex Fourier-Gaussian eigenfunction (S6b ACT)

This part proves the **archimedean analogue of (C2)** from `problem.md`:
the standard complex Gaussian `exp(-π · ‖z‖²)` is a fixed point
(eigenfunction, eigenvalue 1) of the Fourier transform on `ℂ`. It is the
"dual-domain" counterpart of the integral-side identities proved earlier
in Parts 1–5 — instead of integrating the Gaussian against Lebesgue
measure, we apply the Fourier integral and recover the same Gaussian.

The parametric statement `complex_fourier_gaussian` is a direct
specialization of Mathlib's `_root_.fourier_gaussian_innerProductSpace`
at `V := ℂ`. The dimensional exponent `(Module.finrank ℝ V / 2 : ℂ)`
collapses to `1` via `Complex.finrank_real_complex` (`finrank ℝ ℂ = 2`),
and `Complex.cpow_one` reduces `(π / b) ^ (1 : ℂ)` to `π / b`.

The eigenfunction corollary `complex_fourier_gaussian_pi` (at `b = π`)
is the load-bearing archimedean (C2): the factor `π / π = 1` by
`div_self`, and the exponent `-π² · ‖w‖² / π` simplifies to `-π · ‖w‖²`
by `field_simp`, leaving `cexp (-π · ‖w‖²)` — the same Gaussian on the
"Fourier side".

The `normSq` companion exposes the same statement with the algebraic
`Complex.normSq` in place of the analytic `‖·‖²`, paralleling the
S3 ↔ `normSq` companion `complex_gaussian_integral_scaled` ↔
`complex_gaussian_integral_scaled_norm` pattern.

See `research/problems/area-of-circle-oq-05-oq-04/sessions/2026-05-16-s11-prep-s6b-sharpened.md`
for the pre-ACT plan and Mathlib bearer audit (verified at
`lake-manifest.json` SHA `2df2f0150c…`, Mathlib v4.26.0).

The Fourier integral notation `𝓕` resolves through
`Real.instFourierTransform : FourierTransform (V → ℂ) (V → ℂ)` (for
`V = ℂ`, the required `InnerProductSpace ℝ ℂ` instance is
`RCLike.toInnerProductSpaceReal`). -/

/-- **Parametric complex Fourier-Gaussian**: for any `b : ℂ` with
`0 < b.re` and any `w : ℂ`,

    𝓕 (z ↦ exp(-b · ‖z‖²)) w = (π / b) · exp(-π² · ‖w‖² / b).

This is a direct specialization of `_root_.fourier_gaussian_innerProductSpace`
at the 2-dimensional real inner product space `V := ℂ`. The dimensional
exponent `(finrank ℝ ℂ / 2 : ℂ) = (2 / 2 : ℂ) = 1` collapses via
`Complex.finrank_real_complex`, and `Complex.cpow_one` reduces the base
`(π/b) ^ (1 : ℂ)` to `π / b`. -/
theorem complex_fourier_gaussian (b : ℂ) (hb : 0 < b.re) (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-b * ‖z‖ ^ 2)) w
      = (Real.pi / b) * Complex.exp (-(Real.pi : ℂ) ^ 2 * ‖w‖ ^ 2 / b) := by
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb w
  -- Collapse the dimensional exponent `(finrank ℝ ℂ / 2 : ℂ)` to `1`.
  have hfr : ((Module.finrank ℝ ℂ : ℂ) / 2) = (1 : ℂ) := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hfr, Complex.cpow_one] at h
  exact h

/-- **Complex Gaussian self-Fourier identity** (the archimedean analogue
of (C2)): the standard complex Gaussian `exp(-π · ‖z‖²)` is a fixed point
of `𝓕`:

    𝓕 (z ↦ exp(-π · ‖z‖²)) w = exp(-π · ‖w‖²).

This is the complex-side analogue of Mathlib's `_root_.fourier_gaussian_pi`
at the unit scale, and the archimedean analogue of the conjectural p-adic
self-Fourier statement `(F 𝟙_{ℤ_p})(ξ) = 𝟙_{ℤ_p}(ξ)` from problem.md (C2);
see the deferred discussion at the end of this file.

Proof: specialize `complex_fourier_gaussian` at `b = (π : ℂ)`. The
prefactor `π / π = 1` by `div_self` (using `(π : ℂ) ≠ 0`), and the
exponent `-π² · ‖w‖² / π` simplifies to `-π · ‖w‖²` by `field_simp`. -/
theorem complex_fourier_gaussian_pi (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-(Real.pi : ℂ) * ‖z‖ ^ 2)) w
      = Complex.exp (-(Real.pi : ℂ) * ‖w‖ ^ 2) := by
  -- The required positivity hypothesis for the parametric form: `(π : ℂ).re = π > 0`.
  have hbre : (0 : ℝ) < ((Real.pi : ℂ)).re := by
    rw [Complex.ofReal_re]; exact Real.pi_pos
  have h := complex_fourier_gaussian (Real.pi : ℂ) hbre w
  -- Collapse the constant factor `π / π = 1`.
  have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [div_self hπne, one_mul] at h
  -- Simplify the exponent `-π² · ‖w‖² / π = -π · ‖w‖²`.
  have hexp : -(Real.pi : ℂ) ^ 2 * ‖w‖ ^ 2 / (Real.pi : ℂ) =
              -(Real.pi : ℂ) * ‖w‖ ^ 2 := by
    field_simp
  rw [hexp] at h
  exact h

/-- `Complex.normSq` companion of the parametric complex Fourier-Gaussian:

    𝓕 (z ↦ exp(-b · normSq z)) w = (π / b) · exp(-π² · normSq w / b).

The algebraic `Complex.normSq` is `‖·‖²` reduced to a real-valued
polynomial in the real and imaginary parts: `normSq z = z.re² + z.im²`.
The bridge is `Complex.normSq_eq_norm_sq : normSq z = ‖z‖²` (as reals),
applied pointwise and then cast through to ℂ.

This is the Fourier-domain analogue of the `complex_gaussian_integral_scaled`
↔ `complex_gaussian_integral_scaled_norm` pairing (lines 226 ↔ 261). -/
theorem complex_fourier_gaussian_normSq (b : ℂ) (hb : 0 < b.re) (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-b * (Complex.normSq z : ℂ))) w
      = (Real.pi / b) * Complex.exp (-(Real.pi : ℂ) ^ 2 *
          (Complex.normSq w : ℂ) / b) := by
  -- Pointwise cast: `(normSq z : ℂ) = (‖z‖ : ℂ)^2 = ‖z‖^2` (the last
  -- form is how Lean elaborates `‖z‖^2` when expected to be ℂ).
  have key : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = (‖z‖ : ℂ) ^ 2 := fun z => by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [key]
  exact complex_fourier_gaussian b hb w

/-! ## Part 7 — S6b ACT-2: shifted Fourier-Gaussian + density-eigenfunction companion

The two companions deferred from S6b (sessions/2026-05-31-s6b-act-complex-fourier-gaussian.md):

1. `complex_fourier_gaussian_shifted` — direct specialization of
   `_root_.fourier_gaussian_innerProductSpace'` at `V := ℂ`. This is the
   modulation companion of `complex_fourier_gaussian`: a `2πi · ⟪x, z⟫`
   phase in the input becomes an additive `-w ↦ x - w` shift in the
   Fourier-domain Gaussian peak.

2. `complex_fourier_gaussian_density_eigen` — Fourier-eigenfunction
   identity for the normalised complex Gaussian density
   `(1/π) · exp(-π · ‖z‖²)`. This follows from
   `complex_fourier_gaussian_pi` by pulling the constant `(1/π)` out of
   the Fourier integral via linearity (`integral_const_mul`). It is the
   density-form companion of `complex_fourier_gaussian_pi`, exhibiting
   that the normalised Gaussian density on ℂ is a fixed point of `𝓕`
   with eigenvalue `1`.

Both are sorry-free and axiom-free. -/

/-- **Shifted complex Fourier-Gaussian**: for any `b : ℂ` with
`0 < b.re` and `x w : ℂ`,

    𝓕 (z ↦ exp(-b · ‖z‖² + 2π i · ⟪x, z⟫)) w
      = (π / b) · exp(-π² · ‖x - w‖² / b).

This is a direct specialization of
`_root_.fourier_gaussian_innerProductSpace'` at the 2-dimensional real
inner product space `V := ℂ`. The dimensional exponent
`(finrank ℝ ℂ / 2 : ℂ) = (2 / 2 : ℂ) = 1` collapses via
`Complex.finrank_real_complex`, and `Complex.cpow_one` reduces the base
`(π/b) ^ (1 : ℂ)` to `π / b`. -/
theorem complex_fourier_gaussian_shifted (b : ℂ) (hb : 0 < b.re) (x w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-b * ‖z‖ ^ 2
        + 2 * (Real.pi : ℂ) * Complex.I * ((⟪x, z⟫ : ℝ) : ℂ))) w
      = (Real.pi / b) *
          Complex.exp (-(Real.pi : ℂ) ^ 2 * ‖x - w‖ ^ 2 / b) := by
  have h := _root_.fourier_gaussian_innerProductSpace' (V := ℂ) hb x w
  -- Collapse the dimensional exponent `(finrank ℝ ℂ / 2 : ℂ)` to `1`.
  have hfr : ((Module.finrank ℝ ℂ : ℂ) / 2) = (1 : ℂ) := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hfr, Complex.cpow_one] at h
  exact h

/-- **Normalised complex Gaussian density is a Fourier eigenfunction**
(eigenvalue 1): for any `w : ℂ`,

    𝓕 (z ↦ (1/π) · exp(-π · ‖z‖²)) w = (1/π) · exp(-π · ‖w‖²).

This is the density-form companion of `complex_fourier_gaussian_pi`:
the normalised Gaussian density `(1/π) · exp(-π · ‖z‖²)` on ℂ — which
integrates to 1 by `complex_gaussian_integral_normalised` — is a fixed
point of `𝓕` with eigenvalue `1`.

Proof: pull the constant `(1/π)` out of the Fourier integral via
`integral_const_mul` (linearity of the Lebesgue integral), then apply
`complex_fourier_gaussian_pi`. -/
theorem complex_fourier_gaussian_density_eigen (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ (1 / (Real.pi : ℂ)) *
        Complex.exp (-(Real.pi : ℂ) * ‖z‖ ^ 2)) w
      = (1 / (Real.pi : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ‖w‖ ^ 2) := by
  have h := complex_fourier_gaussian_pi w
  rw [fourier_eq] at h
  rw [fourier_eq]
  -- The integrand `𝐞(-⟪z,w⟫) • ((1/π) * exp(...))` decomposes as
  -- `(1/π) * (𝐞(-⟪z,w⟫) • exp(...))` after unfolding both Circle smuls to
  -- multiplications; we then pull `(1/π)` out via `integral_const_mul`.
  have ptw : ∀ z : ℂ,
      (𝐞 (-(⟪z, w⟫ : ℝ))) •
        ((1 / (Real.pi : ℂ)) *
          Complex.exp (-(Real.pi : ℂ) * ‖z‖ ^ 2))
      = (1 / (Real.pi : ℂ)) *
          ((𝐞 (-(⟪z, w⟫ : ℝ))) •
            Complex.exp (-(Real.pi : ℂ) * ‖z‖ ^ 2)) := by
    intro z
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  simp_rw [ptw]
  rw [integral_const_mul, h]

/-! ## Part 8 — S6c ACT-1: Diagonal Schur prerequisite (1-D real second moment)

The load-bearing 1-D real Gaussian second moment for the un-normalised
weight `exp(-x²)`:

    ∫_ℝ x² · exp(-x²) dx = √π / 2.

This is the first step of the S6c diagonal Schur orthogonality assembly
(per session memo
`sessions/2026-06-02-s6c-prep-3-gaussianreal-variance-skeleton.md`).

Proof route: gaussianReal variance shortcut (PREP-3 §3 route 2). The
standard real Gaussian `gaussianReal 0 (1/2 : ℝ≥0)` has pdf
`(√π)⁻¹ · exp(-x²)`. Its variance equals `∫ x² · pdf dx` (since mean = 0)
and is `1/2` by definition. Multiplying through by `√π` gives the claim. -/

section DiagonalSchurPrep

open ProbabilityTheory NNReal

/-- 1-D real second moment of the un-normalised Gaussian:
`∫_ℝ x² · exp(-x²) dx = √π / 2`. Load-bearing prerequisite for the
S6c diagonal Schur orthogonality assembly. -/
theorem integral_sq_exp_neg_sq :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  -- Parameters: μ = 0, v = (1/2 : ℝ≥0). Variance v gives pdf (√π)⁻¹·exp(-x²).
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  have hv_coe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_cast
  -- Step 1. The mean is zero.
  have hmean : ∫ x, x ∂(gaussianReal (0 : ℝ) (1 / 2 : ℝ≥0)) = 0 :=
    integral_id_gaussianReal
  -- Step 2. Variance = ∫ x² (since mean = 0), and variance = 1/2.
  have hvar : ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) (1 / 2 : ℝ≥0)) = (1 / 2 : ℝ) := by
    have h := variance_of_integral_eq_zero
      (X := id) (μ := gaussianReal (0 : ℝ) (1 / 2 : ℝ≥0))
      measurable_id'.aemeasurable hmean
    rw [variance_id_gaussianReal] at h
    simpa [id, hv_coe] using h.symm
  -- Step 3. Bridge to Lebesgue: ∫ f ∂gaussianReal = ∫ pdf · f dx.
  rw [integral_gaussianReal_eq_integral_smul (f := fun x : ℝ => x ^ 2) hv] at hvar
  -- Step 4. Closed-form pdf at (μ = 0, v = 1/2): (√π)⁻¹ · exp(-x²).
  have hpdf : ∀ x : ℝ,
      gaussianPDFReal 0 (1 / 2 : ℝ≥0) x
        = (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    rw [hv_coe, sub_zero,
        show (2 * Real.pi * (1 / 2 : ℝ)) = Real.pi from by ring,
        show (-(x ^ 2) / (2 * (1 / 2 : ℝ))) = -x ^ 2 from by ring]
  -- Step 5. Pull `(√π)⁻¹` out of the integral.
  have hpoint : ∀ x : ℝ,
      gaussianPDFReal 0 (1 / 2 : ℝ≥0) x • (x ^ 2 : ℝ)
        = (Real.sqrt Real.pi)⁻¹ * (x ^ 2 * Real.exp (-x ^ 2)) := by
    intro x
    rw [hpdf x, smul_eq_mul]; ring
  simp_rw [hpoint] at hvar
  rw [integral_const_mul] at hvar
  -- Step 6. Solve: `(√π)⁻¹ · I = 1/2 ⇒ I = √π / 2`, since `√π > 0`.
  have hπ_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp at hvar
  linarith

end DiagonalSchurPrep

/-! ## Status

- `integral_pi_gaussian` : proved (direct from `scaled_gaussian`).
- `complex_gaussian_integral` : proved (Fubini + measure-preserving equiv).
- `complex_gaussian_integral_norm` : proved (corollary of the above).
- `integral_b_gaussian` : proved (re-export of `scaled_gaussian`).
- `complex_gaussian_integral_scaled` : proved (parametric Fubini).
- `complex_gaussian_integral_scaled_norm` : proved (`‖z‖²` form).
- `complex_gaussian_integral_unit_norm` : proved (`b = 1` corollary).
- `complex_gaussian_integral_normalised` : proved (`1/π` density).
- `complex_gaussian_integral_scaled_pow` : proved (n-dim parametric, S4a).
- `complex_gaussian_integral_scaled_pow_normSq` : proved (`normSq` form).
- `complex_gaussian_integral_pow_unit_norm` : proved (n-dim `b = 1`).
- `complex_gaussian_integral_pow_normalised` : proved (`(1/π)ⁿ` density).
- `complex_gaussian_integral_scaled_shifted_norm` : proved (translation-invariant, S5).
- `complex_gaussian_integral_scaled_shifted` : proved (`normSq` form of shifted).
- `complex_gaussian_integral_unit_shifted_norm` : proved (unit-weight shifted).
- `complex_gaussian_density_shifted` : proved (canonical `(c, b)` density).
- `complex_gaussian_integral_scaled_pow_shifted_norm` : proved (n-dim shifted, S6a).
- `complex_gaussian_integral_scaled_pow_shifted_normSq` : proved (`normSq` form of n-dim shifted).
- `complex_gaussian_integral_pow_unit_shifted_norm` : proved (n-dim unit-weight shifted).
- `complex_gaussian_density_pow_shifted` : proved (canonical n-dim `(c, b)` density).
- `complex_fourier_gaussian` : proved (parametric Fourier-Gaussian, S6b).
- `complex_fourier_gaussian_pi` : proved (self-Fourier eigenfunction at `b = π`, load-bearing archimedean (C2)).
- `complex_fourier_gaussian_normSq` : proved (`Complex.normSq` form of the parametric Fourier-Gaussian).
- `complex_fourier_gaussian_shifted` : proved (modulation companion, direct `_root_.fourier_gaussian_innerProductSpace'` specialization at `V := ℂ`, S6b ACT-2).
- `complex_fourier_gaussian_density_eigen` : proved (the normalised density `(1/π) · exp(-π · ‖z‖²)` is a Fourier eigenfunction with eigenvalue `1`, via `integral_const_mul` + `complex_fourier_gaussian_pi`, S6b ACT-2).
- `integral_sq_exp_neg_sq` : proved (1-D real second moment `∫ x²·exp(-x²) = √π/2`, via `gaussianReal 0 (1/2 : ℝ≥0)` variance shortcut, S6c ACT-1).

All theorems above are sorry-free and axiom-free.

## Deferred — p-adic case (C2 in problem.md)

The p-adic self-Fourier identity

    (F 𝟙_{ℤ_p})(ξ) = 𝟙_{ℤ_p}(ξ),
    so in particular `∫_{ℚ_p} 𝟙_{ℤ_p}(x) ψ_p(0 · x) dx = μ(ℤ_p) = 1`

is the intended p-adic analogue (cf. `problem.md` §C2). Formalizing
this requires two Mathlib milestones currently absent at v4.26.0:

1. **Standard p-adic additive character** `ψ_p : ℚ_p → ℂ` with
   `ψ_p|_{ℤ_p} = 1` and `ψ_p(p^{-n}) = e^{2πi · a_n}`. Mathlib's
   `Mathlib.NumberTheory.Padics.AddChar` only treats `ℤ_p → R` characters
   into a `ℤ_p`-algebra `R` — the *dual* direction.

2. **Explicit `MeasureTheory.Measure ℚ_p`** with `μ(ℤ_p) = 1`. The
   general Haar machinery in `Mathlib.MeasureTheory.Measure.Haar.Basic`
   applies (ℚ_p is locally compact via `PadicInt.ProperSpace`), but the
   specific normalised instance is not exposed.

Once those are upstream, the proof of (C2) follows the same Fubini-style
factorisation as `complex_gaussian_integral`, replacing the Gaussian
integral on each real factor with the character-sum identity
`∑_{a ∈ ℤ/p^k ℤ} e^{2πi a / p^k} = 0` for `k ≥ 1`, packaged ultrametrically.

The complex case in this file is the "scalar" companion to that
non-trivial p-adic Fourier-fixed-point statement.
-/

end ComplexGaussianCircle
