import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Faulhaber's Fifth-Power Sum: ∑ k⁵ = n²(n+1)²(2n²+2n−1)/12

## Open Question (nicomachus-sum-of-cubes-oq-04)

The fifth-power (`p = 5`) member of the Faulhaber family, extending the parent
Nicomachus sum-of-cubes identity `∑ k³ = (∑ k)²` and the sibling fourth-power
entry.  The classical closed form is

    1⁵ + 2⁵ + ⋯ + n⁵ = n²(n+1)²(2n²+2n−1)/12.

Indexing over `range (n+1)` (the `k = 0` term vanishes) the sum reads
`∑_{k ≤ n} k⁵`.

Check: `n=1 → 1 = 1·4·3/12`, `n=2 → 1+32 = 33 = 4·9·11/12`,
`n=3 → 1+32+243 = 276 = 9·16·23/12`.

## Result

A fully machine-checked, self-contained proof by induction.

The closed form `n²(n+1)²(2n²+2n−1)/12` carries both a division and (after
clearing it) a subtraction — `12·∑ k⁵ = 2n⁶ + 6n⁵ + 5n⁴ − n²` — and truncated
subtraction is the enemy of `ring` over ℕ.  We sidestep both by proving the
**subtraction-free, division-free** equivalent

    `12·(∑_{k ≤ n} k⁵) + n² = 2n⁶ + 6n⁵ + 5n⁴`        (`sum_fifth_powers_add`),

obtained by adding `n²` to both sides.  Every term is a genuine natural number,
so the inductive step closes by a single polynomial identity (`ring` for the
algebra, `omega` to splice it with the hypothesis, treating the powers as opaque
atoms).  The headline factored form is then recovered over ℤ
(`twelve_mul_sum_fifth`, where the subtraction is honest) and finally over ℚ with
the explicit `/12` (`sum_fifth_powers_rat`).

## Novelty

The gallery already carries the Nicomachus cube sum (`p = 3`), the odd-cube sum,
and the `p = 4` Faulhaber closed form.  This file supplies the next member,
`p = 5`, mirroring the additive clear-denominator technique used for the sibling
power-sum entries.  Mathlib has Bernoulli-polynomial Faulhaber machinery but not
this elementary factored integer identity.

0 sorries, 0 axioms.
-/

namespace NicomachusFifthPowers

open Finset

/-- **Subtraction-free fifth-power identity.**  Adding `n²` to both sides of the
headline `12·∑ k⁵ = 2n⁶ + 6n⁵ + 5n⁴ − n²` clears the truncated subtraction, so
the whole statement lives cleanly in ℕ:

`12·(∑_{k ≤ n} k⁵) + n² = 2n⁶ + 6n⁵ + 5n⁴`.

The induction step is a pure polynomial identity; `omega` splices it together
with the inductive hypothesis (treating the powers as opaque atoms). -/
theorem sum_fifth_powers_add (n : ℕ) :
    12 * (∑ k ∈ range (n + 1), k ^ 5) + n ^ 2
      = 2 * n ^ 6 + 6 * n ^ 5 + 5 * n ^ 4 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    -- The algebraic heart, a subtraction-free polynomial identity over ℕ:
    have key : 2 * m ^ 6 + 6 * m ^ 5 + 5 * m ^ 4 + 12 * (m + 1) ^ 5 + (m + 1) ^ 2
        = 2 * (m + 1) ^ 6 + 6 * (m + 1) ^ 5 + 5 * (m + 1) ^ 4 + m ^ 2 := by ring
    -- `ih` and `key` are linear in the nonlinear atoms; `omega` closes the goal.
    omega

/-- **Factored form over ℤ.**  Twelve times the sum of the first `n` fifth powers
equals the classical product `n²(n+1)²(2n²+2n−1)`:

`12·(∑_{k ≤ n} k⁵) = n²(n+1)²(2n²+2n−1)`.

Stated over ℤ so the factor `2n²+2n−1` uses honest subtraction. -/
theorem twelve_mul_sum_fifth (n : ℕ) :
    12 * (∑ k ∈ range (n + 1), (k : ℤ) ^ 5)
      = (n : ℤ) ^ 2 * (n + 1) ^ 2 * (2 * n ^ 2 + 2 * n - 1) := by
  have h := sum_fifth_powers_add n
  have hℤ := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at hℤ
  -- hℤ : 12·(∑ ↑k⁵) + ↑n² = 2·↑n⁶ + 6·↑n⁵ + 5·↑n⁴
  have hsum : 12 * (∑ k ∈ range (n + 1), (k : ℤ) ^ 5)
      = 2 * (n : ℤ) ^ 6 + 6 * (n : ℤ) ^ 5 + 5 * (n : ℤ) ^ 4 - (n : ℤ) ^ 2 := by
    linarith [hℤ]
  rw [hsum]; ring

/-- **Headline closed form over ℚ.**  The Faulhaber `p = 5` identity in its
classical divided form:

`∑_{k ≤ n} k⁵ = n²(n+1)²(2n²+2n−1)/12`. -/
theorem sum_fifth_powers_rat (n : ℕ) :
    (∑ k ∈ range (n + 1), (k : ℚ) ^ 5)
      = (n : ℚ) ^ 2 * (n + 1) ^ 2 * (2 * n ^ 2 + 2 * n - 1) / 12 := by
  have h := sum_fifth_powers_add n
  have hℚ := congrArg (Nat.cast : ℕ → ℚ) h
  push_cast at hℚ
  -- hℚ : 12·(∑ ↑k⁵) + ↑n² = 2·↑n⁶ + 6·↑n⁵ + 5·↑n⁴
  have hsum : (∑ k ∈ range (n + 1), (k : ℚ) ^ 5)
      = (2 * (n : ℚ) ^ 6 + 6 * (n : ℚ) ^ 5 + 5 * (n : ℚ) ^ 4 - (n : ℚ) ^ 2) / 12 := by
    linarith [hℚ]
  rw [hsum]; ring

/-- Sanity check: `∑_{k ≤ 3} k⁵ = 1 + 32 + 243 = 276`. -/
example : ∑ k ∈ range 4, k ^ 5 = 276 := by decide

/-- Sanity check (factored): `12·∑_{k ≤ 3} k⁵ = 9·16·23 = 3312`. -/
example : 12 * (∑ k ∈ range 4, k ^ 5) = 3312 := by decide

end NicomachusFifthPowers
