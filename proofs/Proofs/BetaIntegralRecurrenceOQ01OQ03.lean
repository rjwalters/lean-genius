/-
# Beta Integral OQ-01 (leaf oq-03): the symmetric Beta density on [0,1] and its real integral

The diagonal Beta value `B(n+1, n+1) = (n!)²/(2n+1)!` is, on the parent and sibling
entries, established over ℂ via Mathlib's `Complex.betaIntegral` and the Gamma
relation:

* parent `BetaIntegralRecurrence.betaIntegral_nat_nat`: `B(m+1,n+1) = m!·n!/(m+n+1)!`;
* sibling `BetaCentralBinomial`: `B(n+1,n+1) = 1/((2n+1)·C(2n,n))`.

This leaf supplies the **real-variable** statement those entries do not give, and the
probabilistic content it unlocks. We bring `Complex.betaIntegral ((n:ℂ)+1) ((n:ℂ)+1)`
down to ℝ — its integrand `x^(u-1)(1-x)^(v-1)` is, on the diagonal with `u = v = n+1`
and `x ∈ [0,1]`, the real polynomial `x^n (1-x)^n` cast into ℂ — to prove:

* `integral_diag_eq_factorial` : `∫ x in 0..1, x^n (1-x)^n = (n!)²/(2n+1)!`
  (the real Euler integral of the symmetric Beta integrand);
* `integral_diag_central_binom` : the same integral equals `1/((2n+1)·C(2n,n))`;
* `betaDensity_integral_eq_one` : the **normalization of the symmetric Beta(n+1,n+1)
  density** — `∫ x in 0..1, x^n (1-x)^n / B = 1`, where `B = (n!)²/(2n+1)!`, so that
  `x ↦ x^n(1-x)^n / B` is a probability density on `[0,1]`.

The bridge ℂ → ℝ (`Complex.cpow_natCast` to turn the complex powers into monoid powers,
then `intervalIntegral.integral_ofReal`) is the new ingredient; the closed-form value is
reused from the parent. This is the real-analysis / probability face of the diagonal Beta
value, complementary to the complex `betaIntegral` siblings.

*Reference:* [erdosproblems.com] Beta–Gamma; Mathlib `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`.
-/

import Proofs.BetaIntegralRecurrence
import Proofs.BetaCentralBinomial
import Mathlib.Tactic

open Complex intervalIntegral

namespace BetaIntegralRecurrenceOQ01OQ03

/-- **Bridge to the real line.** The complex diagonal Beta integral is the real integral
of the symmetric integrand `x^n (1-x)^n`, cast into ℂ. On `[0,1]` the complex powers
`(x:ℂ)^((n+1)-1)` collapse to monoid powers via `Complex.cpow_natCast`, and the integral
descends through `ofReal`. -/
theorem ofReal_integral_diag (n : ℕ) :
    (((∫ x in (0:ℝ)..1, x ^ n * (1 - x) ^ n) : ℝ) : ℂ)
      = betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1) := by
  rw [betaIntegral, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  have he : ((n : ℂ) + 1) - 1 = (n : ℂ) := by ring
  rw [he, Complex.cpow_natCast, Complex.cpow_natCast]
  push_cast
  ring

/-- **The real Euler integral of the symmetric Beta integrand.**
`∫₀¹ x^n (1-x)^n dx = (n!)² / (2n+1)!`. -/
theorem integral_diag_eq_factorial (n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ n * (1 - x) ^ n
      = (n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ) := by
  have h := ofReal_integral_diag n
  rw [BetaIntegralRecurrence.betaIntegral_nat_nat n n] at h
  have hrhs :
      (n.factorial : ℂ) * (n.factorial : ℂ) / ((n + n + 1).factorial : ℂ)
        = (((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) : ℂ) := by
    rw [two_mul]; push_cast; ring
  rw [hrhs] at h
  exact_mod_cast h

/-- The same real integral as a central-binomial reciprocal:
`∫₀¹ x^n (1-x)^n dx = 1 / ((2n+1)·C(2n,n))`. -/
theorem integral_diag_central_binom (n : ℕ) :
    ∫ x in (0:ℝ)..1, x ^ n * (1 - x) ^ n
      = 1 / ((2 * n + 1) * Nat.choose (2 * n) n : ℝ) := by
  rw [integral_diag_eq_factorial]
  -- (2n+1)! = (2n+1)·C(2n,n)·(n!·n!), reusing the sibling's factorial factorization
  have hfact : ((2 * n + 1).factorial : ℝ)
      = (2 * n + 1 : ℝ) * (Nat.choose (2 * n) n : ℝ) * ((n.factorial : ℝ) * (n.factorial : ℝ)) := by
    have h := BetaCentralBinomial.factorial_two_mul_succ n
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  have hn : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [hfact]
  field_simp

/-- **Normalization of the symmetric Beta(n+1, n+1) density on [0,1].**
With `B = (n!)²/(2n+1)! = ∫₀¹ x^n(1-x)^n dx`, the function `x ↦ x^n(1-x)^n / B`
integrates to `1`, hence is a probability density on `[0,1]`. -/
theorem betaDensity_integral_eq_one (n : ℕ) :
    ∫ x in (0:ℝ)..1,
        x ^ n * (1 - x) ^ n / ((n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ)) = 1 := by
  have hn : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hd : (0:ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hB : (0:ℝ) < (n.factorial : ℝ) ^ 2 / ((2 * n + 1).factorial : ℝ) := by positivity
  rw [intervalIntegral.integral_div, integral_diag_eq_factorial]
  exact div_self (ne_of_gt hB)

end BetaIntegralRecurrenceOQ01OQ03
