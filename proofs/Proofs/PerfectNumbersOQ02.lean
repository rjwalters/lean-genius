import Mathlib

/-
# Perfect Numbers OQ-02: The Abundancy Index and the Reciprocal-Divisor Characterization

## Context (parent perfect-numbers: the Euclid–Euler theorem)

A positive integer `n` is **perfect** when it equals the sum of its proper divisors
(`6 = 1+2+3`, `28 = 1+2+4+7+14`), equivalently `σ(n) = 2n`. The parent develops the
Euclid–Euler classification of even perfect numbers.

## What this file proves

The **abundancy index** of `n` is `I(n) = σ(n)/n`, and a clean, convention-free way to write it
is as the **sum of the reciprocals of the divisors of `n`**:

> **`I(n) = ∑_{d ∣ n} 1/d`.**

The reason is the divisor involution `d ↦ n/d`: pairing each divisor with its cofactor turns
`∑_{d∣n} 1/d` into `(1/n)·∑_{d∣n} (n/d) = (1/n)·∑_{d∣n} d = σ(n)/n`. From this the perfect-number
condition becomes the elegant statement

> **`n` is perfect ⟺ `∑_{d ∣ n} 1/d = 2`.**

So a perfect number is exactly one whose divisor reciprocals sum to `2`; for `6`, indeed
`1/1 + 1/2 + 1/3 + 1/6 = 2`. We give the index identity, the iff, and the concrete value at the
first two perfect numbers `6` and `28`.

Tags: number-theory, perfect-numbers, divisors, abundancy, sigma, sum-of-divisors

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

open Finset

namespace PerfectNumbersOQ02

/-- The **abundancy index** of `n`, written as the sum of the reciprocals of its divisors:
    `I(n) = ∑_{d ∣ n} 1/d`. (For `n > 0` this equals `σ(n)/n`.) -/
noncomputable def abundancyIndex (n : ℕ) : ℚ := ∑ d ∈ n.divisors, (d : ℚ)⁻¹

/-- **The reciprocal-divisor sum is `σ(n)/n`.** Pairing each divisor `d` with its cofactor
    `n/d` (the involution `d ↦ n/d` on the divisors) gives
    `∑_{d∣n} 1/d = (1/n)·∑_{d∣n} d = σ(n)/n`. -/
theorem abundancyIndex_eq_sigma_div {n : ℕ} (hn : 0 < n) :
    abundancyIndex n = (∑ i ∈ n.divisors, (i : ℕ) : ℚ) / n := by
  have hrw : ∀ d ∈ n.divisors, (d : ℚ)⁻¹ = ((n / d : ℕ) : ℚ) / n := by
    intro d hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
    have hd0 : (d : ℚ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd; exact_mod_cast this.ne'
    rw [Nat.cast_div hdvd hd0]
    field_simp
  rw [abundancyIndex, Finset.sum_congr rfl hrw, ← Finset.sum_div, Nat.sum_div_divisors,
    ← Nat.cast_sum]

/-- **The reciprocal-divisor characterization of perfect numbers.**
    `n` is perfect iff the reciprocals of its divisors sum to `2`:
    `n.Perfect ↔ ∑_{d ∣ n} 1/d = 2`. -/
theorem perfect_iff_abundancyIndex_eq_two {n : ℕ} (hn : 0 < n) :
    n.Perfect ↔ abundancyIndex n = 2 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, abundancyIndex_eq_sigma_div hn, div_eq_iff hn0,
    ← Nat.cast_sum]
  constructor
  · intro h; rw [h]; push_cast; ring
  · intro h; exact_mod_cast h

/-- A perfect number has divisor reciprocals summing to exactly `2`. -/
theorem abundancyIndex_eq_two_of_perfect {n : ℕ} (hn : 0 < n) (hp : n.Perfect) :
    ∑ d ∈ n.divisors, (d : ℚ)⁻¹ = 2 :=
  (perfect_iff_abundancyIndex_eq_two hn).mp hp

/-! ## Concrete values at the first perfect numbers -/

/-- `6` is a perfect number. -/
theorem perfect_six : Nat.Perfect 6 :=
  (Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)).mpr (by decide)

/-- `28` is a perfect number. -/
theorem perfect_twentyEight : Nat.Perfect 28 :=
  (Nat.perfect_iff_sum_divisors_eq_two_mul (by norm_num)).mpr (by decide)

/-- `6` is perfect: `1/1 + 1/2 + 1/3 + 1/6 = 2`. -/
theorem abundancyIndex_six : abundancyIndex 6 = 2 :=
  (perfect_iff_abundancyIndex_eq_two (by norm_num)).mp perfect_six

/-- `28` is perfect: its divisor reciprocals sum to `2`. -/
theorem abundancyIndex_twentyEight : abundancyIndex 28 = 2 :=
  (perfect_iff_abundancyIndex_eq_two (by norm_num)).mp perfect_twentyEight

end PerfectNumbersOQ02

/-
## Summary

The abundancy index and the reciprocal-divisor characterization of perfect numbers:

- `abundancyIndex`:                      `I(n) = ∑_{d∣n} 1/d`.
- `abundancyIndex_eq_sigma_div`:         `I(n) = σ(n)/n`, via the divisor involution `d ↦ n/d`.
- `perfect_iff_abundancyIndex_eq_two`:   **`n` is perfect ⟺ `∑_{d∣n} 1/d = 2`.**
- `abundancyIndex_six`, `abundancyIndex_twentyEight`: the value `2` at `6` and `28`.

Uses Mathlib's `Nat.sum_div_divisors` (the divisor involution) and
`Nat.perfect_iff_sum_divisors_eq_two_mul`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
