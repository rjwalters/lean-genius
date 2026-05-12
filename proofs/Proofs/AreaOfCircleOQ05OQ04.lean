/-
Area of Circle OQ-05-OQ-04 (S2a): The Complex Gaussian Integral

Proves the complex Gaussian identity

    ∫_ℂ exp(-π · ‖z‖²) dz = 1

i.e. the indicator that the Gaussian density `e^{-π |z|²}` on ℂ integrates
to 1 against the standard Lebesgue measure on ℂ (induced by the canonical
identification ℂ ≃ ℝ²).

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

/-! ## Status

- `integral_pi_gaussian` : proved (direct from `scaled_gaussian`).
- `complex_gaussian_integral` : proved (Fubini + measure-preserving equiv).
- `complex_gaussian_integral_norm` : proved (corollary of the above).

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
