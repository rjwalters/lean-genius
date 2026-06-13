import Mathlib

/-
# Beta Integral for the n-Dimensional Angular Averaging Identity

## Open Question: buffons-needle-oq-01-oq-01-oq-04-oq-01

The angular averaging identity for the n-dimensional Cauchy–Crofton formula
reduces, via the polar-coordinate decomposition of the sphere integral on
`S^{n-1}`, to the one-dimensional **Beta integral**

  ∫_0^{π/2} cos θ · sin^{n-2} θ dθ = 1/(n-1).

This is the analytic core flagged as the key missing piece for the general
`n ≥ 3` case (the 2D case is proved axiom-free in
`BuffonsNeedleOQ01OQ01OQ04OQ01.lean`). Its value `1/(n-1)` supplies the
`sphereArea (n-2)/((n:ℝ)-1)` proportionality factor in the angular average.

This file is **self-contained** (depends only on Mathlib) and proves the
identity from the fundamental theorem of calculus, with antiderivative
`F(θ) = sin^{m+1}(θ)/(m+1)`, equivalently the substitution `u = sin θ`:
`∫_0^1 uᵐ du = 1/(m+1)`. **No axioms, no sorries.**

## Main results

1. `integral_cos_mul_sin_pow`  : ∫_0^{π/2} cos θ · sinᵐ θ dθ = 1/(m+1)
2. `integral_cos_mul_sin_pow_dim` : ∫_0^{π/2} cos θ · sin^{n-2} θ dθ = 1/(n-1), n ≥ 2
-/

open Real intervalIntegral MeasureTheory

namespace BuffonsNeedleOQ01OQ01OQ04OQ01Beta

/-- ∫_0^{π/2} cos θ · sinᵐ θ dθ = 1/(m+1).

    Proof by the fundamental theorem of calculus with antiderivative
    `F(θ) = sin^{m+1}(θ)/(m+1)`, since `F'(θ) = cos θ · sinᵐ θ`. This is the
    substitution `u = sin θ` in closed form: `∫_0^1 uᵐ du = 1/(m+1)`. -/
theorem integral_cos_mul_sin_pow (m : ℕ) :
    ∫ θ in (0:ℝ)..(π/2), Real.cos θ * Real.sin θ ^ m = 1 / ((m : ℝ) + 1) := by
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (π/2),
      HasDerivAt (fun x => Real.sin x ^ (m + 1) / ((m : ℝ) + 1))
        (Real.cos θ * Real.sin θ ^ m) θ := by
    intro θ _
    have hp : HasDerivAt (fun x => Real.sin x ^ (m + 1))
        ((↑(m + 1)) * Real.sin θ ^ (m + 1 - 1) * Real.cos θ) θ :=
      (Real.hasDerivAt_sin θ).pow (m + 1)
    rw [Nat.add_sub_cancel] at hp
    have hd := hp.div_const ((m : ℝ) + 1)
    have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
    convert hd using 1
    push_cast
    field_simp
  have hcont : Continuous (fun θ : ℝ => Real.cos θ * Real.sin θ ^ m) :=
    Real.continuous_cos.mul (Real.continuous_sin.pow m)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (hcont.intervalIntegrable 0 (π/2)),
    Real.sin_pi_div_two, Real.sin_zero]
  simp [zero_pow (Nat.succ_ne_zero m)]

/-- **Beta Integral** (n ≥ 2): ∫_0^{π/2} cos θ · sin^{n-2} θ dθ = 1/(n-1).

    This is the analytic core of the n-dimensional angular averaging identity:
    the polar-coordinate decomposition of the sphere integral reduces the angular
    average to this one-dimensional integral, whose value `1/(n-1)` supplies the
    `sphereArea (n-2)/((n:ℝ)-1)` factor in the n-dimensional Cauchy–Crofton
    constant. -/
theorem integral_cos_mul_sin_pow_dim (n : ℕ) (hn : 2 ≤ n) :
    ∫ θ in (0:ℝ)..(π/2), Real.cos θ * Real.sin θ ^ (n - 2) = 1 / ((n : ℝ) - 1) := by
  have hcast : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [integral_cos_mul_sin_pow (n - 2), hcast]

end BuffonsNeedleOQ01OQ01OQ04OQ01Beta
