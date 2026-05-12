/-
Area of Circle OQ-05-OQ-04 (S2a + S3): The Complex Gaussian Integral

Proves the complex Gaussian identities

    ∫_ℂ exp(-π · ‖z‖²) dz = 1               (S2a, b = π specialisation)
    ∫_ℂ exp(-(b · ‖z‖²)) dz = π / b         (S3, parametric in b > 0)

and the natural corollaries `∫_ℂ exp(-‖z‖²) dz = π` (unit weight,
"complex Gaussian = area of unit disc") and the probability density
`∫_ℂ (1/π) · exp(-‖z‖²) dz = 1`.

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
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Proofs.AreaOfCircleOQ05

namespace ComplexGaussianCircle

open MeasureTheory MeasureTheory.Measure Real Complex

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

/-! ## Status

- `integral_pi_gaussian` : proved (direct from `scaled_gaussian`).
- `complex_gaussian_integral` : proved (Fubini + measure-preserving equiv).
- `complex_gaussian_integral_norm` : proved (corollary of the above).
- `integral_b_gaussian` : proved (re-export of `scaled_gaussian`).
- `complex_gaussian_integral_scaled` : proved (parametric Fubini).
- `complex_gaussian_integral_scaled_norm` : proved (`‖z‖²` form).
- `complex_gaussian_integral_unit_norm` : proved (`b = 1` corollary).
- `complex_gaussian_integral_normalised` : proved (`1/π` density).

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
