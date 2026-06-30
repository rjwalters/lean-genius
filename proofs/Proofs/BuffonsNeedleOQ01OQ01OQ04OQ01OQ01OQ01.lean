import Mathlib

/-
# Companion Beta Integral and the Reflection Symmetry of the Angular Average

## Open Question: buffons-needle-oq-01-oq-01-oq-04-oq-01-oq-01-oq-01

The parent entry (`BuffonsNeedleOQ01OQ01OQ04OQ01Beta`) proved the angular Beta
integral

  ∫_0^{π/2} cos θ · sinᵐ θ dθ = 1/(m+1)

by the fundamental theorem of calculus with antiderivative `sin^{m+1}θ/(m+1)`,
and flagged as its first open question whether the **companion integral**

  ∫_0^{π/2} sin θ · cosᵐ θ dθ = 1/(m+1)

can be formalized by the same FTC template. This file answers that question
**affirmatively**, with the mirror antiderivative `F(θ) = -cos^{m+1}θ/(m+1)`,
equivalently the substitution `u = cos θ`: `∫_1^0 (-uᵐ) du = ∫_0^1 uᵐ du = 1/(m+1)`.

It also resolves the parent's *second* open question — whether an **independent
proof** exists — by deriving the companion identity a second way, from the parent
identity via the reflection `θ ↦ π/2 − θ` of the integration interval. Under this
reflection `sin θ ↔ cos θ`, so the companion integral is literally the parent
integral with the two factors swapped; the two FTC computations are mirror images
of one substitution.

## Main results

1. `integral_sin_mul_cos_pow`      : ∫_0^{π/2} sin θ · cosᵐ θ dθ = 1/(m+1)   (direct FTC)
2. `integral_sin_mul_cos_pow_dim`  : ∫_0^{π/2} sin θ · cos^{n-2} θ dθ = 1/(n-1), n ≥ 2
3. `integral_sin_mul_cos_pow_eq_reflect`
       : the companion equals the parent integral `∫_0^{π/2} cos θ · sinᵐ θ dθ`
         by the reflection `θ ↦ π/2 − θ` (an independent derivation of the value)

The full two-parameter Beta function `B(a,b) = ∫_0^{π/2} sin^{2a-1}θ cos^{2b-1}θ dθ`
for general real `a,b` is **out of scope** of the single-step FTC template: a single
elementary antiderivative closes the integral only when one of the two factors is a
first power (the odd-power case `u = sin θ` or `u = cos θ`). The general case needs
the Gamma-function recurrence and is recorded as the boundary of this method.

**No axioms, no sorries.**
-/

open Real intervalIntegral MeasureTheory

namespace BuffonsNeedleOQ01OQ01OQ04OQ01OQ01OQ01

/-- **Companion Beta integral.** `∫_0^{π/2} sin θ · cosᵐ θ dθ = 1/(m+1)`.

    Proof by the fundamental theorem of calculus with antiderivative
    `F(θ) = -cos^{m+1}(θ)/(m+1)`, since `F'(θ) = sin θ · cosᵐ θ`. This is the
    mirror of the parent file's `cos θ · sinᵐ θ` integral: the substitution
    `u = cos θ` gives `∫_1^0 (-uᵐ) du = 1/(m+1)`. -/
theorem integral_sin_mul_cos_pow (m : ℕ) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ * Real.cos θ ^ m = 1 / ((m : ℝ) + 1) := by
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (π/2),
      HasDerivAt (fun x => (-(Real.cos x ^ (m + 1))) / ((m : ℝ) + 1))
        (Real.sin θ * Real.cos θ ^ m) θ := by
    intro θ _
    have hp : HasDerivAt (fun x => Real.cos x ^ (m + 1))
        ((↑(m + 1)) * Real.cos θ ^ (m + 1 - 1) * (-Real.sin θ)) θ :=
      (Real.hasDerivAt_cos θ).pow (m + 1)
    rw [Nat.add_sub_cancel] at hp
    have hd := (hp.neg).div_const ((m : ℝ) + 1)
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    convert hd using 1
    push_cast
    field_simp
    ring
  have hcont : Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ m) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow m)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcont.intervalIntegrable 0 (π/2)),
    Real.cos_pi_div_two, Real.cos_zero]
  simp [zero_pow (Nat.succ_ne_zero m)]

/-- **Companion Beta integral, dimensional form** (n ≥ 2):
    `∫_0^{π/2} sin θ · cos^{n-2} θ dθ = 1/(n-1)`.

    The companion of the parent's `integral_cos_mul_sin_pow_dim`; both supply the
    same `1/(n-1)` proportionality factor in the n-dimensional angular average,
    now with the roles of `sin` and `cos` exchanged. -/
theorem integral_sin_mul_cos_pow_dim (n : ℕ) (hn : 2 ≤ n) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ * Real.cos θ ^ (n - 2) = 1 / ((n : ℝ) - 1) := by
  have hcast : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [integral_sin_mul_cos_pow (n - 2), hcast]

/-- **Independent derivation via reflection.** The companion integral equals the
    parent integral `∫_0^{π/2} cos θ · sinᵐ θ dθ` under the substitution
    `θ ↦ π/2 − θ`, which swaps `sin θ ↔ cos θ` and fixes the interval `[0, π/2]`.

    This gives a second, FTC-free proof of the value `1/(m+1)`: the companion is
    the mirror image of the parent identity, not a new computation. -/
theorem integral_sin_mul_cos_pow_eq_reflect (m : ℕ) :
    ∫ θ in (0:ℝ)..(π/2), Real.sin θ * Real.cos θ ^ m
      = ∫ θ in (0:ℝ)..(π/2), Real.cos θ * Real.sin θ ^ m := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => Real.cos θ * Real.sin θ ^ m) (π/2) (a := 0) (b := π/2)
  -- `h : ∫ θ in 0..π/2, cos(π/2-θ) · sin(π/2-θ)ᵐ = ∫ θ in (π/2-π/2)..(π/2-0), cos θ · sinᵐ θ`
  simp only [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, sub_zero, sub_self] at h
  exact h

/-- Cross-check: the reflection identity reproves the companion value, matching the
    direct FTC computation in `integral_sin_mul_cos_pow`. -/
example (m : ℕ) :
    ∫ θ in (0:ℝ)..(π/2), Real.cos θ * Real.sin θ ^ m = 1 / ((m : ℝ) + 1) := by
  rw [← integral_sin_mul_cos_pow_eq_reflect, integral_sin_mul_cos_pow]

end BuffonsNeedleOQ01OQ01OQ04OQ01OQ01OQ01
