import Mathlib
import Proofs.BetaIntegralRecurrenceOQ01OQ02OQ01
import Proofs.StirlingFormulaOQ03OQ02

/-
# Stirling Asymptotic of the Diagonal Half-Integer Beta Value

## What This Proves

The parent entry `beta-integral-recurrence-oq-01-oq-02-oq-01` established the exact
closed form of the diagonal of half-integer Beta values

  `B(n+½, n+½) = π · C(2n,n) / 4^{2n}`   (`betaIntegral_diag_half_centralBinom`),

with `C(2n,n) = Nat.centralBinom n` the central binomial coefficient.  The sibling
Stirling entry `stirling-formula-oq-03-oq-02` proved the central binomial asymptotic

  `C(2n,n) · √(πn) / 4ⁿ → 1`,   i.e.   `C(2n,n) ~ 4ⁿ / √(πn)`
  (`StirlingFormulaOQ03OQ02.centralBinom_asymptotic`).

Substituting the asymptotic into the exact diagonal value gives the large-`n`
behaviour of the Beta value itself:

  **`betaDiag_isEquivalent`**:
    `B(n+½, n+½)  ~  √(π/n) · 4⁻ⁿ`   as `n → ∞`.

## A correction to the naive guess

A first guess is that `B(n+½,n+½)` should be asymptotic to `√(π/n)` — the half-line
Gaussian-type tail.  **That is false.**  The central binomial only grows like `4ⁿ`,
not `4^{2n}`, so the `4^{2n}` in the denominator of the exact formula leaves an
*exponentially decaying* residual factor `4⁻ⁿ`:

  `B(n+½,n+½) = π·C(2n,n)/4^{2n} ~ π·(4ⁿ/√(πn))/4^{2n} = √(π/n)·4⁻ⁿ`.

So the correct asymptotic carries the `4⁻ⁿ` factor and `B(n+½,n+½) → 0`
geometrically, not merely like `n^{-1/2}`.  This matches the classical diagonal
Beta asymptotic `B(x,x) ~ 2^{1-2x}·√(π/x)`: at `x = n+½` the prefactor
`2^{1-2x} = 4⁻ⁿ`.

## Approach

The reciprocal of the claimed equivalent is exactly the normalising factor that
turns the exact value into the central-binomial ratio:

  `B(n+½,n+½) · (√(π/n)·4⁻ⁿ)⁻¹ = B(n+½,n+½) · 4ⁿ · √(πn)/π = C(2n,n)·√(πn)/4ⁿ`,

a *pure field identity* (the `π`'s cancel and `4^{2n} = 4ⁿ·4ⁿ`), needing no
square-root manipulation.  Hence the normalised ratio tends to `1` by
`centralBinom_asymptotic`, and `isEquivalent_iff_tendsto_one` upgrades that to the
`IsEquivalent` statement.
-/

open Filter Topology Asymptotics
open scoped Real Nat

namespace BetaIntegralRecurrenceOQ01OQ02OQ01OQ01

/-- The real closed form of the diagonal half-integer Beta value,
`B(n+½, n+½) = π · C(2n,n) / 4^{2n}`. -/
noncomputable def betaDiag (n : ℕ) : ℝ :=
  π * (Nat.centralBinom n : ℝ) / 4 ^ (2 * n)

/-- The complex Beta integral on the half-integer diagonal equals the real closed
form `betaDiag n` (cast to `ℂ`); so the asymptotic below describes the genuine
Beta value. -/
theorem betaIntegral_eq_betaDiag (n : ℕ) :
    Complex.betaIntegral ((n : ℂ) + 1 / 2) ((n : ℂ) + 1 / 2) = (betaDiag n : ℂ) := by
  rw [BetaIntegralRecurrenceOQ01OQ02OQ01.betaIntegral_diag_half_centralBinom]
  unfold betaDiag
  push_cast
  ring

/-- The diagonal value is strictly positive. -/
theorem betaDiag_pos (n : ℕ) : 0 < betaDiag n := by
  unfold betaDiag
  have : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.centralBinom_pos n
  positivity

/-- **Normalised ratio tends to 1.**

`B(n+½,n+½) · 4ⁿ · √(πn) / π → 1`.  The normalising factor `4ⁿ·√(πn)/π` is exactly
the reciprocal of the equivalent `√(π/n)·4⁻ⁿ`; matching it to the central-binomial
asymptotic is a pure field identity. -/
theorem betaDiag_normalized_tendsto :
    Tendsto (fun n : ℕ => betaDiag n * 4 ^ n * Real.sqrt (π * n) / π) atTop (𝓝 1) := by
  refine StirlingFormulaOQ03OQ02.centralBinom_asymptotic.congr (fun n => ?_)
  -- goal: cb n * √(πn) / 4ⁿ = betaDiag n * 4ⁿ * √(πn) / π
  show StirlingFormulaOQ03OQ02.cb n * Real.sqrt (π * n) / 4 ^ n
      = betaDiag n * 4 ^ n * Real.sqrt (π * n) / π
  unfold StirlingFormulaOQ03OQ02.cb betaDiag
  have h4 : (4 : ℝ) ^ (2 * n) = 4 ^ n * 4 ^ n := by rw [two_mul, pow_add]
  have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hπ : (π : ℝ) ≠ 0 := Real.pi_pos.ne'
  rw [h4]
  field_simp

/-- **Stirling asymptotic of the diagonal half-integer Beta value.**

`B(n+½, n+½) ~ √(π/n) · 4⁻ⁿ` as `n → ∞`.

Note the exponentially small factor `4⁻ⁿ`: the naive guess `B(n+½,n+½) ~ √(π/n)`
is *false*, because the central binomial grows only like `4ⁿ` against the `4^{2n}`
in the denominator. -/
theorem betaDiag_isEquivalent :
    (fun n : ℕ => betaDiag n) ~[atTop] (fun n : ℕ => Real.sqrt (π / n) / 4 ^ n) := by
  -- the equivalent is eventually nonzero (for n ≥ 1)
  have hg : ∀ᶠ n : ℕ in atTop, Real.sqrt (π / n) / 4 ^ n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 : (0 : ℝ) < π / n := by positivity
    have h2 := Real.sqrt_pos.mpr h1
    positivity
  rw [isEquivalent_iff_tendsto_one hg]
  -- ratio betaDiag n / (√(π/n)/4ⁿ) = betaDiag n * 4ⁿ * √(πn)/π  (eventually, n ≥ 1)
  refine betaDiag_normalized_tendsto.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ0 : (π : ℝ) ≠ 0 := hπ.ne'
  have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hsπn : Real.sqrt (π * n) ≠ 0 := by
    have : (0 : ℝ) < π * n := by positivity
    exact (Real.sqrt_pos.mpr this).ne'
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  -- √(π/n) = √(πn)/n, reducing all square roots to the single atom √(πn)
  have hsplit : Real.sqrt (π / n) = Real.sqrt (π * n) / n := by
    rw [Real.sqrt_div Real.pi_nonneg, Real.sqrt_mul Real.pi_nonneg,
      div_eq_div_iff hsn hn0, mul_assoc, Real.mul_self_sqrt hnpos.le]
  -- goal: betaDiag n * 4ⁿ * √(πn)/π = betaDiag n / (√(π/n)/4ⁿ)
  simp only [Pi.div_apply]
  rw [hsplit]
  field_simp
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ π * (n : ℝ))]
  ring

end BetaIntegralRecurrenceOQ01OQ02OQ01OQ01
