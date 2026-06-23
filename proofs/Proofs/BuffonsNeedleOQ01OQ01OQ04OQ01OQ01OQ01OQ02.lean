import Mathlib

/-
# Exponent-Swap Reflection Symmetry of the Half-Period Trigonometric Integral

## Open Question: buffons-needle-oq-01-oq-01-oq-04-oq-01-oq-01-oq-01-oq-02

The parent entry (`BuffonsNeedleOQ01OQ01OQ04OQ01OQ01OQ01`) proved a *single-power*
instance of the reflection symmetry: under `θ ↦ π/2 − θ` the integral
`∫_0^{π/2} sin θ · cosᵐ θ dθ` equals `∫_0^{π/2} cos θ · sinᵐ θ dθ`. It flagged as
its **second open question** whether that reflection argument packages into one
clean, reusable lemma — the statement that the half-period trigonometric integral
is invariant under **swapping the two exponents**:

  ∫_0^{π/2} sinᵃ θ · cosᵇ θ dθ = ∫_0^{π/2} sinᵇ θ · cosᵃ θ dθ.

This file answers that affirmatively. The single mechanism is the reflection
`θ ↦ π/2 − θ`, which fixes the interval `[0, π/2]` and exchanges `sin ↔ cos` by the
*unconditional* identities `sin(π/2−θ) = cos θ` and `cos(π/2−θ) = sin θ`. No
antiderivative, no integrability hypothesis, and no positivity assumption is
needed — the swap is a pure change of variables, so it holds verbatim for both
natural-number powers and arbitrary real (`rpow`) exponents.

## Main results

1. `integral_sin_pow_mul_cos_pow_swap`   — ℕ exponents: the headline reusable lemma.
2. `integral_sin_rpow_mul_cos_rpow_swap` — real exponents (`Real.rpow`), strictly
   more general; this is the form that meets the trigonometric Beta integral.
3. `integral_beta_trig_symm`             — Euler Beta symmetry `B(x,y) = B(y,x)` in
   its trigonometric guise, an immediate corollary of (2).
4. `integral_sin_mul_cos_pow_eq_reflect` — the parent's single-power identity
   recovered as the `a = 1` corollary of (1).

The link to Mathlib's `Real.betaIntegral` / `Real.Gamma` (the half-angle
substitution `t = sin²θ` and the Gamma recurrence) is the natural next boundary
and is left to the Beta/Gamma API; this file isolates the *symmetry* content,
which is purely the reflection and needs none of that machinery.

**No axioms, no sorries.**
-/

open Real intervalIntegral MeasureTheory

namespace BuffonsNeedleOQ01OQ01OQ04OQ01OQ01OQ01OQ02

/-- **Exponent-swap reflection symmetry (natural-number powers).**

    `∫_0^{π/2} sinᵃ θ · cosᵇ θ dθ = ∫_0^{π/2} sinᵇ θ · cosᵃ θ dθ`.

    Proof: the reflection `θ ↦ π/2 − θ` (`intervalIntegral.integral_comp_sub_left`)
    fixes the interval `[0, π/2]` and, by `sin(π/2−θ) = cos θ` and
    `cos(π/2−θ) = sin θ`, turns the integrand `sinᵃ θ · cosᵇ θ` into
    `cosᵃ θ · sinᵇ θ`. Both factors are simply transposed, so the value is
    unchanged — no FTC, no integrability side condition. -/
theorem integral_sin_pow_mul_cos_pow_swap (a b : ℕ) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ a * Real.cos θ ^ b
      = ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ b * Real.cos θ ^ a := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => Real.sin θ ^ a * Real.cos θ ^ b) (π / 2) (a := 0) (b := π / 2)
  -- `h : ∫ θ in 0..π/2, cosᵃ θ · sinᵇ θ = ∫ θ in 0..π/2, sinᵃ θ · cosᵇ θ`
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, sub_zero, sub_self] at h
  rw [← h]
  exact intervalIntegral.integral_congr (fun θ _ => mul_comm _ _)

/-- **Exponent-swap reflection symmetry (arbitrary real exponents).**

    `∫_0^{π/2} sinᵃ θ · cosᵇ θ dθ = ∫_0^{π/2} sinᵇ θ · cosᵃ θ dθ` for `a b : ℝ`,
    where the powers are `Real.rpow`.

    The reflection `θ ↦ π/2 − θ` rewrites the *bases* via `sin(π/2−θ) = cos θ`,
    `cos(π/2−θ) = sin θ`, so the argument is insensitive to whether the exponents
    are natural numbers or reals — strictly generalizing the ℕ version, and the
    form that meets the Euler Beta integral. -/
theorem integral_sin_rpow_mul_cos_rpow_swap (a b : ℝ) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ a * Real.cos θ ^ b
      = ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ b * Real.cos θ ^ a := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => Real.sin θ ^ a * Real.cos θ ^ b) (π / 2) (a := 0) (b := π / 2)
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, sub_zero, sub_self] at h
  rw [← h]
  exact intervalIntegral.integral_congr (fun θ _ => mul_comm _ _)

/-- **Euler Beta symmetry in trigonometric form.** With the classical trigonometric
    representation `B(x, y) = 2 ∫_0^{π/2} sin^{2x−1}θ · cos^{2y−1}θ dθ`, the Beta
    function's symmetry `B(x, y) = B(y, x)` is exactly the exponent swap

      `∫_0^{π/2} sin^{2x−1}θ · cos^{2y−1}θ dθ = ∫_0^{π/2} sin^{2y−1}θ · cos^{2x−1}θ dθ`,

    here obtained directly from the reflection, with no Gamma-function input. -/
theorem integral_beta_trig_symm (x y : ℝ) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ (2 * x - 1) * Real.cos θ ^ (2 * y - 1)
      = ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ (2 * y - 1) * Real.cos θ ^ (2 * x - 1) :=
  integral_sin_rpow_mul_cos_rpow_swap (2 * x - 1) (2 * y - 1)

/-- **The parent's reflection identity, recovered as the `a = 1` corollary.**

    The parent file proved `∫_0^{π/2} sin θ · cosᵐ θ = ∫_0^{π/2} cos θ · sinᵐ θ` by
    a bespoke reflection. It is the special case `a = 1`, `b = m` of the general
    swap lemma (using `sin θ ^ 1 = sin θ`, `cos θ ^ 1 = cos θ`), confirming the
    headline lemma is a genuine generalization. -/
theorem integral_sin_mul_cos_pow_eq_reflect (m : ℕ) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ * Real.cos θ ^ m
      = ∫ θ in (0:ℝ)..(π/2), Real.cos θ * Real.sin θ ^ m := by
  have h := integral_sin_pow_mul_cos_pow_swap 1 m
  simp only [pow_one] at h
  rw [h]
  exact intervalIntegral.integral_congr (fun θ _ => mul_comm _ _)

/-- Cross-check: the diagonal `a = b` is fixed by the swap (it relates the integral
    to itself), so the symmetry is vacuous there — a sanity check that the lemma is
    stated in the right direction. -/
example (a : ℕ) :
    (∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ a * Real.cos θ ^ a)
      = ∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ a * Real.cos θ ^ a :=
  integral_sin_pow_mul_cos_pow_swap a a

end BuffonsNeedleOQ01OQ01OQ04OQ01OQ01OQ01OQ02
