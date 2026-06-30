import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Faulhaber's Fourth-Power Sum: ∑ k⁴ = n(n+1)(2n+1)(3n²+3n−1)/30

## Open Question (nicomachus-sum-of-cubes-oq-02)

The fourth-power (`p = 4`) member of the Faulhaber family, extending the parent
Nicomachus sum-of-cubes identity `∑ k³ = (∑ k)²`.  The classical closed form is

    1⁴ + 2⁴ + ⋯ + n⁴ = n(n+1)(2n+1)(3n²+3n−1)/30.

Indexing over `range (n+1)` (the `k = 0` term vanishes) the sum reads
`∑_{k ≤ n} k⁴`.

Check: `n=1 → 1 = 1·2·3·5/30`, `n=2 → 1+16 = 17 = 2·3·5·17/30`,
`n=3 → 1+16+81 = 98 = 3·4·7·35/30`.

## Result

A fully machine-checked, self-contained proof by induction.

The closed form `n(n+1)(2n+1)(3n²+3n−1)/30` carries both a division and (after
clearing it) a subtraction — `30·∑ k⁴ = 6n⁵ + 15n⁴ + 10n³ − n` — and truncated
subtraction is the enemy of `ring` over ℕ.  We sidestep both by proving the
**subtraction-free, division-free** equivalent

    `30·(∑_{k ≤ n} k⁴) + n = 6n⁵ + 15n⁴ + 10n³`        (`sum_fourth_powers_add`),

obtained by adding `n` to both sides.  Every term is a genuine natural number, so
the inductive step closes by a single polynomial identity (`ring` for the
algebra, `omega` to splice it with the hypothesis).  The headline factored form
is then recovered over ℤ (`thirty_mul_sum_fourth`, where the subtraction is
honest) and finally over ℚ with the explicit `/30` (`sum_fourth_powers_rat`).

## Novelty

Mathlib has the Gauss triangular-number identity and, via this gallery, the
Nicomachus cube sum and the odd-cube sum, but not the `p = 4` Faulhaber closed
form.  This file supplies it, mirroring the additive clear-denominator technique
used for the sibling power-sum entries.

0 sorries, 0 axioms.
-/

namespace NicomachusFourthPowers

open Finset

/-- **Subtraction-free fourth-power identity.**  Adding `n` to both sides of the
headline `30·∑ k⁴ = 6n⁵ + 15n⁴ + 10n³ − n` clears the truncated subtraction, so
the whole statement lives cleanly in ℕ:

`30·(∑_{k ≤ n} k⁴) + n = 6n⁵ + 15n⁴ + 10n³`.

The induction step is a pure polynomial identity; `omega` splices it together
with the inductive hypothesis (treating the powers as opaque atoms). -/
theorem sum_fourth_powers_add (n : ℕ) :
    30 * (∑ k ∈ range (n + 1), k ^ 4) + n = 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^ 3 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    -- The algebraic heart, a subtraction-free polynomial identity over ℕ:
    have key : 6 * m ^ 5 + 15 * m ^ 4 + 10 * m ^ 3 + 30 * (m + 1) ^ 4 + 1
        = 6 * (m + 1) ^ 5 + 15 * (m + 1) ^ 4 + 10 * (m + 1) ^ 3 := by ring
    -- `ih` and `key` are linear in the nonlinear atoms; `omega` closes the goal.
    omega

/-- **Factored form over ℤ.**  Thirty times the sum of the first `n` fourth powers
equals the classical product `n(n+1)(2n+1)(3n²+3n−1)`:

`30·(∑_{k ≤ n} k⁴) = n(n+1)(2n+1)(3n²+3n−1)`.

Stated over ℤ so the factor `3n²+3n−1` uses honest subtraction. -/
theorem thirty_mul_sum_fourth (n : ℕ) :
    30 * (∑ k ∈ range (n + 1), (k : ℤ) ^ 4)
      = (n : ℤ) * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) := by
  have h := sum_fourth_powers_add n
  have hℤ := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at hℤ
  -- hℤ : 30·(∑ ↑k⁴) + ↑n = 6·↑n⁵ + 15·↑n⁴ + 10·↑n³
  have hsum : 30 * (∑ k ∈ range (n + 1), (k : ℤ) ^ 4)
      = 6 * (n : ℤ) ^ 5 + 15 * (n : ℤ) ^ 4 + 10 * (n : ℤ) ^ 3 - (n : ℤ) := by
    linarith [hℤ]
  rw [hsum]; ring

/-- **Headline closed form over ℚ.**  The Faulhaber `p = 4` identity in its
classical divided form:

`∑_{k ≤ n} k⁴ = n(n+1)(2n+1)(3n²+3n−1)/30`. -/
theorem sum_fourth_powers_rat (n : ℕ) :
    (∑ k ∈ range (n + 1), (k : ℚ) ^ 4)
      = (n : ℚ) * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) / 30 := by
  have h := sum_fourth_powers_add n
  have hℚ := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at hℚ
  -- hℚ : 30·(∑ ↑k⁴) + ↑n = 6·↑n⁵ + 15·↑n⁴ + 10·↑n³
  have hsum : (∑ k ∈ range (n + 1), (k : ℚ) ^ 4)
      = (6 * (n : ℚ) ^ 5 + 15 * (n : ℚ) ^ 4 + 10 * (n : ℚ) ^ 3 - (n : ℚ)) / 30 := by
    linarith [hℚ]
  rw [hsum]; ring

/-- Sanity check: `∑_{k ≤ 3} k⁴ = 1 + 16 + 81 = 98`. -/
example : ∑ k ∈ range 4, k ^ 4 = 98 := by decide

/-- Sanity check (factored): `30·∑_{k ≤ 3} k⁴ = 3·4·7·35 = 2940`. -/
example : 30 * (∑ k ∈ range 4, k ^ 4) = 2940 := by decide

end NicomachusFourthPowers
