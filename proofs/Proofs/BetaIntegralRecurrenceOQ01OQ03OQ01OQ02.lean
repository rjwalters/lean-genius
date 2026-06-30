/-
# Beta Integral OQ-01 (leaf oq-03-oq-01-oq-02): low-order moments of the integer Beta distribution

The parent leaf `BetaIntegralRecurrenceOQ01OQ03OQ01` supplied the **off-diagonal real Euler
Beta integral at integer arguments**

  `∫₀¹ xᵐ(1-x)ⁿ dx = m!·n! / (m+n+1)!`     (`integral_offdiag_eq_factorial`).

This is exactly the normalising constant `B(m+1, n+1)` of the Beta(m+1, n+1) distribution,
whose density on `[0,1]` is `xᵐ(1-x)ⁿ / B(m+1,n+1)`.  This leaf answers the parent's open
question OQ[1] — *can the mean be read off as a one-line corollary by shifting `m ↦ m+1`?* —
and then pushes through the **full low-order moment structure** of the distribution, all from
the single parent integral:

* `mean_eq`            — `E[X]   = (m+1) / (m+n+2)`               (the requested corollary),
* `second_moment_eq`  — `E[X²]  = (m+1)(m+2) / ((m+n+2)(m+n+3))`,
* `variance_eq`       — `Var(X) = E[X²] − E[X]² = (m+1)(n+1) / ((m+n+2)²(m+n+3))`.

Each moment is a ratio of weighted integrals `∫₀¹ xʲ·xᵐ(1-x)ⁿ / ∫₀¹ xᵐ(1-x)ⁿ`, and the weight
`xʲ` is absorbed by the index shift `m ↦ m+j` so that the parent's closed form applies to both
numerator and denominator.  The factorial bookkeeping then collapses to elementary algebra.

Specialising to `α = m+1`, `β = n+1`, these are the textbook moments of `Beta(α, β)`:
`α/(α+β)`, `α(α+1)/((α+β)(α+β+1))`, and `αβ/((α+β)²(α+β+1))`.

*Reference:* moments of the Beta distribution; Euler Beta function at integer arguments.
-/

import Proofs.BetaIntegralRecurrenceOQ01OQ03OQ01
import Mathlib.Tactic

open intervalIntegral MeasureTheory

namespace BetaIntegralRecurrenceOQ01OQ03OQ01OQ02

/-- Shorthand for the parent's off-diagonal integer Beta integral. -/
private alias offdiag := BetaIntegralRecurrenceOQ01OQ03OQ01.integral_offdiag_eq_factorial

/-! ## The normalising constant is positive

The denominator `∫₀¹ xᵐ(1-x)ⁿ = m!·n!/(m+n+1)! ` is strictly positive, so every moment ratio
below is a genuine division (not `x/0`). -/

/-- `B(m+1, n+1) = ∫₀¹ xᵐ(1-x)ⁿ dx > 0`. -/
theorem normalising_pos (m n : ℕ) :
    (0:ℝ) < ∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n := by
  rw [offdiag m n]
  have hm : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hn : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hd : (0:ℝ) < ((m + n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  positivity

/-! ## The mean (parent OQ[1])

`E[X] = ∫₀¹ x·xᵐ(1-x)ⁿ / ∫₀¹ xᵐ(1-x)ⁿ = (m+1)/(m+n+2)`. The numerator weight `x` shifts
`m ↦ m+1`, and `(m+1)!·(m+n+1)! / (m!·(m+n+2)!) = (m+1)/(m+n+2)`. -/
theorem mean_eq (m n : ℕ) :
    (∫ x in (0:ℝ)..1, x * (x ^ m * (1 - x) ^ n))
        / (∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n)
      = ((m : ℝ) + 1) / ((m : ℝ) + n + 2) := by
  rw [show (∫ x in (0:ℝ)..1, x * (x ^ m * (1 - x) ^ n))
        = ∫ x in (0:ℝ)..1, x ^ (m + 1) * (1 - x) ^ n from
        integral_congr (fun x _ => by ring)]
  rw [offdiag (m + 1) n, offdiag m n]
  -- index normalisation and factorial peeling
  have hidx : m + 1 + n + 1 = (m + n + 1) + 1 := by ring
  have h1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h2 : (((m + n + 1) + 1).factorial : ℝ)
      = ((m : ℝ) + n + 2) * ((m + n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hidx, h1, h2]
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hc : ((m + n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hd : ((m : ℝ) + n + 2) ≠ 0 := by positivity
  field_simp

/-! ## The second raw moment

`E[X²] = ∫₀¹ x²·xᵐ(1-x)ⁿ / ∫₀¹ xᵐ(1-x)ⁿ = (m+1)(m+2)/((m+n+2)(m+n+3))`. The weight `x²`
shifts `m ↦ m+2`. -/
theorem second_moment_eq (m n : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ 2 * (x ^ m * (1 - x) ^ n))
        / (∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n)
      = ((m : ℝ) + 1) * ((m : ℝ) + 2) / (((m : ℝ) + n + 2) * ((m : ℝ) + n + 3)) := by
  rw [show (∫ x in (0:ℝ)..1, x ^ 2 * (x ^ m * (1 - x) ^ n))
        = ∫ x in (0:ℝ)..1, x ^ (m + 2) * (1 - x) ^ n from
        integral_congr (fun x _ => by ring)]
  rw [offdiag (m + 2) n, offdiag m n]
  have hidx : m + 2 + n + 1 = (m + n + 1) + 1 + 1 := by ring
  have h1 : ((m + 2).factorial : ℝ)
      = ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have h2 : ((((m + n + 1) + 1) + 1).factorial : ℝ)
      = ((m : ℝ) + n + 3) * ((m : ℝ) + n + 2) * ((m + n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [hidx, h1, h2]
  have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hc : ((m + n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hd2 : ((m : ℝ) + n + 2) ≠ 0 := by positivity
  have hd3 : ((m : ℝ) + n + 3) ≠ 0 := by positivity
  field_simp

/-! ## The variance

`Var(X) = E[X²] − E[X]² = (m+1)(n+1) / ((m+n+2)²(m+n+3))`, combining the two moments above. -/
theorem variance_eq (m n : ℕ) :
    (∫ x in (0:ℝ)..1, x ^ 2 * (x ^ m * (1 - x) ^ n))
        / (∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n)
      - ((∫ x in (0:ℝ)..1, x * (x ^ m * (1 - x) ^ n))
        / (∫ x in (0:ℝ)..1, x ^ m * (1 - x) ^ n)) ^ 2
      = ((m : ℝ) + 1) * ((n : ℝ) + 1)
          / ((((m : ℝ) + n + 2) ^ 2) * ((m : ℝ) + n + 3)) := by
  rw [second_moment_eq, mean_eq]
  have hd2 : ((m : ℝ) + n + 2) ≠ 0 := by positivity
  have hd3 : ((m : ℝ) + n + 3) ≠ 0 := by positivity
  field_simp
  ring

end BetaIntegralRecurrenceOQ01OQ03OQ01OQ02
