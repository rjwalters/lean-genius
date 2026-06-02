import Mathlib

/-
# Wallis Half-Period Integral for Even Powers

Companion to `AmgmInequalityOQ04OQ03.lean`.

Discharges one of the four remaining "legs" of the axiomatized identity
  `ellipticK_eq_hyp2F1 : K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)`
in the companion file.

The Wallis half-period integral closed form:
  `∫₀^{π/2} sin^{2n}θ dθ = (π/2) · centralBinom n / 4^n`
is the closed-form needed for the term-by-term integration argument that
proves the hypergeometric series representation of K(k). Mathlib has the
full-period analogue `Real.integral_sin_pow_even` over `[0, π]`, and the
Wallis product file builds on it, but the half-period closed form needed by
the elliptic integral substitution is not packaged directly.

## Proof Outline

Use the Mathlib reduction formula `intervalIntegral.integral_sin_pow`:
  `∫_a^b sin x ^ (n+2)
    = (sin a ^ (n+1) · cos a − sin b ^ (n+1) · cos b)/(n+2)
      + ((n+1)/(n+2)) · ∫_a^b sin x ^ n`.

Specialized to `[0, π/2]`: `sin 0 = 0` and `cos(π/2) = 0`, so both boundary
terms vanish, leaving the clean recurrence
  `W(n+2) = ((n+1)/(n+2)) · W(n)`
where `W(n) := ∫₀^{π/2} sin^n θ dθ`. Induction on `n` then yields the
closed form for even powers, threaded through the central-binomial
recurrence `Nat.succ_mul_centralBinom_succ`:
  `(n+1) · centralBinom (n+1) = 2 · (2n+1) · centralBinom n`.

## Status
- [x] `wallisHalf_zero` : W(0) = π/2
- [x] `wallisHalf_recurrence` : W(n+2) = ((n+1)/(n+2)) · W(n)
- [x] `wallisHalf_even` : W(2n) = (π/2) · centralBinom n / 4^n  (main)

Axioms: 0
Sorries: 0
-/

namespace AmgmInequalityOQ04OQ03Wallis

open Real intervalIntegral MeasureTheory

/-- The Wallis half-period integral: `W(n) = ∫₀^{π/2} sin^n θ dθ`. -/
noncomputable def wallisHalf (n : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..π / 2, Real.sin θ ^ n

/-- Base case: `W(0) = π/2`. -/
theorem wallisHalf_zero : wallisHalf 0 = π / 2 := by
  unfold wallisHalf
  simp

/-- Reduction formula on `[0, π/2]`: both boundary terms in
    `integral_sin_pow` vanish (`sin 0 = 0`, `cos(π/2) = 0`), giving the
    clean half-period recurrence
      `W(n+2) = ((n+1)/(n+2)) · W(n)`. -/
theorem wallisHalf_recurrence (n : ℕ) :
    wallisHalf (n + 2) = ((n + 1 : ℝ) / (n + 2)) * wallisHalf n := by
  unfold wallisHalf
  rw [integral_sin_pow]
  have h0 : (0 : ℝ) ^ (n + 1) = 0 := by rw [pow_succ, mul_zero]
  rw [Real.sin_zero, Real.cos_pi_div_two, h0]
  ring

/-- **Closed form for even powers** (the Wallis integral):
    `W(2n) = (π/2) · centralBinom n / 4^n`.

    This is the closed form needed for the term-by-term integration step of
    the hypergeometric series representation of the complete elliptic
    integral `K(k) = (π/2) · ₂F₁(1/2, 1/2; 1; k²)`. -/
theorem wallisHalf_even (n : ℕ) :
    wallisHalf (2 * n) = (π / 2) * ((Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n) := by
  induction n with
  | zero =>
      simp [wallisHalf_zero]
  | succ k ih =>
      have hrec : wallisHalf (2 * (k + 1))
          = ((2 * (k : ℝ) + 1) / (2 * k + 2)) * wallisHalf (2 * k) := by
        have hidx : 2 * (k + 1) = (2 * k) + 2 := by ring
        rw [hidx, wallisHalf_recurrence]
        push_cast
        ring
      have hcb : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
          = 2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ k
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have h4k : ((4 : ℝ) ^ k) ≠ 0 := by positivity
      have hc1 : (Nat.centralBinom (k + 1) : ℝ)
          = 2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) / ((k : ℝ) + 1) := by
        rw [eq_div_iff hk1]
        linear_combination hcb
      rw [hrec, ih, hc1, pow_succ]
      field_simp
      ring

end AmgmInequalityOQ04OQ03Wallis
