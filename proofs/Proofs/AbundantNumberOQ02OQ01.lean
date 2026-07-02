/-
  The smallest odd abundant number *not divisible by 3* is

      5391411025 = 5² · 7 · 11 · 13 · 17 · 19 · 23 · 29.

  Background.  A positive integer `n` is *abundant* when the sum of its proper
  divisors exceeds `n`, equivalently `σ(n) > 2n` where `σ = σ₁` is the
  sum-of-divisors function.  The smallest abundant number is 12, the smallest
  *odd* abundant number is 945 = 3³·5·7 (see `AbundantNumberOQ02.lean`).  Once
  the factor 3 is forbidden the smallest example jumps dramatically: the answer
  is the eight-prime number above, with

      σ(5391411025) = 31·8·12·14·18·20·24·30 = 10799308800
                    > 10782822050 = 2·5391411025,

  an abundance margin of only 16486750 (the ratio σ(n)/n ≈ 2.00306 barely
  clears 2 — odd numbers coprime to 3 are "only just" abundant).

  What this file proves (the **witness / membership** half of the full
  resolution).  We establish, axiom-free, that 5391411025 genuinely is

    * odd,
    * not divisible by 3, and
    * abundant,

  hence a member of the set `{ n | Odd n ∧ ¬ 3 ∣ n ∧ Abundant n }`, certifying
  it as an *upper bound* for the least such number.

  Method.  Unlike the `n < 945` case in `AbundantNumberOQ02.lean`, abundance
  here cannot be checked by reducing a divisor sum over `n ≈ 5.4·10⁹`: any
  `decide`/`native_decide` that iterates divisors of a ten-digit number is
  hopeless.  Instead we use the **multiplicativity of σ**
  (`isMultiplicative_sigma`): splitting `n` into its pairwise-coprime prime-power
  factors lets `σ(n)` be assembled from the eight tiny values `σ(5²), σ(7), …,
  σ(29)`, each of which *is* a trivial divisor-sum computation.  No
  `native_decide` is used, so the result carries no `Lean.ofReduceBool`.

  The *minimality* half (the lower bound).  That no odd `m < 5391411025`
  coprime to 3 is abundant is a bounded statement over a range of ~5.4 billion,
  far beyond any kernel or compiled enumeration (the `sigmaFast` O(n)-per-number
  kernel reduction used for the 945 bound would require ~10¹⁹ kernel operations
  here).  It is therefore proved *structurally* rather than by brute force, and
  now lives in the companion files accompanying this one:

    * `…SevenPrimeExponents.lean` assembles the capstone
      `odd_abundant_coprime_three_ge_witness : Odd n → ¬ 3 ∣ n → Abundant n →
      5391411025 ≤ n` from three exhaustive shapes for an odd abundant `n`
      coprime to 3 lying below the witness;
    * `…GeneralBound.lean`, `…Squarefree.lean`, `…OmegaSevenPrimes.lean` and the
      other companions dispatch the squarefree, `ω(n) ≥ 8`, and residual
      `ω(n) = 7` cases via the abundancy-index / prime-exponent structural
      argument (no enumeration).

  Combined with the membership certificate below, this establishes that
  5391411025 is *exactly* the least odd abundant number coprime to 3.  All nine
  files are axiom-free (foundational axioms only; no `native_decide`, no
  `sorryAx`).  This file itself contributes only the witness / membership half.
-/
import Mathlib

namespace AbundantNumberOQ02OQ01

open Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The witness number `5391411025 = 5²·7·11·13·17·19·23·29`. -/
abbrev N : ℕ := 5391411025

/-- `σ₁` of a small prime power, by direct reduction of its divisor sum.
These are the eight atoms the multiplicative assembly multiplies together. -/
theorem sigma_25 : σ 1 25 = 31 := by rw [sigma_one_apply]; decide
theorem sigma_7  : σ 1 7  = 8  := by rw [sigma_one_apply]; decide
theorem sigma_11 : σ 1 11 = 12 := by rw [sigma_one_apply]; decide
theorem sigma_13 : σ 1 13 = 14 := by rw [sigma_one_apply]; decide
theorem sigma_17 : σ 1 17 = 18 := by rw [sigma_one_apply]; decide
theorem sigma_19 : σ 1 19 = 20 := by rw [sigma_one_apply]; decide
theorem sigma_23 : σ 1 23 = 24 := by rw [sigma_one_apply]; decide
theorem sigma_29 : σ 1 29 = 30 := by rw [sigma_one_apply]; decide

/-- **The divisor sum of the witness.**  `σ(5391411025) = 10799308800`,
computed from the prime-power factorisation via multiplicativity of `σ`.
The coprimality side conditions are discharged by `norm_num` (which evaluates
`Nat.gcd`); `Nat.gcd` itself does not kernel-reduce, so `decide` is avoided. -/
theorem sigma_N : σ 1 N = 10799308800 := by
  have e : (N : ℕ) = 25 * (7 * (11 * (13 * (17 * (19 * (23 * 29)))))) := by norm_num
  rw [e,
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
    sigma_25, sigma_7, sigma_11, sigma_13, sigma_17, sigma_19, sigma_23, sigma_29]
  norm_num

/-- Abundance is equivalent to `2n < σ(n)` for the divisor sum `σ = σ₁`:
`σ(n) = (∑ proper divisors) + n`, so `2n < σ(n) ↔ n < ∑ proper divisors`. -/
theorem abundant_iff_two_mul_lt_sigma {n : ℕ} : Nat.Abundant n ↔ 2 * n < σ 1 n := by
  rw [Nat.Abundant, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- **5391411025 is abundant.**  `σ(N) = 10799308800 > 10782822050 = 2N`. -/
theorem abundant_N : Nat.Abundant N := by
  rw [abundant_iff_two_mul_lt_sigma, sigma_N]
  norm_num

/-- **5391411025 is odd.** -/
theorem odd_N : Odd N := by decide

/-- **5391411025 is not divisible by 3.** -/
theorem not_three_dvd_N : ¬ (3 ∣ N) := by decide

/-- **Membership / upper-bound certificate.**  5391411025 is an odd abundant
number coprime to 3, hence belongs to the set whose least element the open
question identifies.  (Minimality — the matching lower bound — is proved in the
companion files; see the file header.) -/
theorem mem_odd_three_free_abundant :
    N ∈ {n : ℕ | Odd n ∧ ¬ (3 ∣ n) ∧ Nat.Abundant n} :=
  ⟨odd_N, not_three_dvd_N, abundant_N⟩

-- Axiom audit: must show ONLY the foundational axioms (propext, Classical.choice,
-- Quot.sound) and in particular NOT `Lean.ofReduceBool` (no `native_decide`) or
-- `sorryAx`.
#print axioms mem_odd_three_free_abundant

end AbundantNumberOQ02OQ01
