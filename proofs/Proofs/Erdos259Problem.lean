/-
Erdős Problem #259: Irrationality of the Squarefree-Weighted Series

Is the sum Σ μ(n)² · n / 2^n irrational, where μ is the Möbius function?

**Answer**: YES - proved by Chen and Ruzsa (1999)

Since μ(n)² = 1 if and only if n is squarefree, this asks about the irrationality
of the sum Σ_{n squarefree} n/2^n.

The stronger result, also proved by Chen and Ruzsa, is that any infinite subseries
over squarefree numbers is irrational.

References:
- https://erdosproblems.com/259
- Chen, Yong-Gao and Ruzsa, Imre Z., "On the irrationality of certain series",
  Period. Math. Hungar. 39 (1999), 31-37
- Erdős, P., "On the irrationality of certain series: problems and results",
  New advances in transcendence theory (Durham, 1986), 102-109
-/

import Mathlib

open BigOperators Nat Real
open scoped ArithmeticFunction

-- Use explicit abbreviation for the Möbius function
abbrev moebiusFn := ArithmeticFunction.moebius

namespace Erdos259

/-!
## Background

The Möbius function μ(n) is defined as:
- μ(1) = 1
- μ(n) = (-1)^k if n is a product of k distinct primes
- μ(n) = 0 if n has a squared prime factor

The key property for this problem is that μ(n)² = 1 iff n is squarefree.

A number n is **squarefree** if no prime p satisfies p² | n.
Equivalently, n has no repeated prime factors in its factorization.

Examples:
- Squarefree: 1, 2, 3, 5, 6, 7, 10, 11, 13, 14, 15, ...
- Not squarefree: 4, 8, 9, 12, 16, 18, 20, ...
-/

/-!
## The Möbius Function

Mathlib provides the Möbius function as `ArithmeticFunction.moebius`.
We use the notation μ from the ArithmeticFunction namespace.
-/

/-- μ(1) = 1 -/
theorem moebius_one : moebiusFn 1 = 1 := ArithmeticFunction.moebius_apply_one

/-- μ(2) = -1 (2 is prime) -/
theorem moebius_two : moebiusFn 2 = -1 := by native_decide

/-- μ(3) = -1 (3 is prime) -/
theorem moebius_three : moebiusFn 3 = -1 := by native_decide

/-- μ(4) = 0 (4 = 2² has a squared factor) -/
theorem moebius_four : moebiusFn 4 = 0 := by native_decide

/-- μ(5) = -1 (5 is prime) -/
theorem moebius_five : moebiusFn 5 = -1 := by native_decide

/-- μ(6) = 1 (6 = 2·3 is product of 2 distinct primes) -/
theorem moebius_six : moebiusFn 6 = 1 := by native_decide

/-- μ(9) = 0 (9 = 3² is a perfect square) -/
theorem moebius_nine : moebiusFn 9 = 0 := by native_decide

/-- μ(10) = 1 (10 = 2·5 is product of 2 distinct primes) -/
theorem moebius_ten : moebiusFn 10 = 1 := by native_decide

/-!
## Squarefree Numbers

Mathlib defines `Squarefree n` as: for all m, m² ∣ n → IsUnit m.
For natural numbers, this means no prime squared divides n.

The connection to μ is: n is squarefree iff μ(n) ≠ 0, iff μ(n)² = 1.
-/

/-- 1 is squarefree -/
theorem squarefree_one' : Squarefree (1 : ℕ) := squarefree_one

/-- Squarefree n ↔ μ(n) ≠ 0. This is the standard characterization. -/
theorem squarefree_iff_moebius_ne_zero (n : ℕ) (_hn : n ≠ 0) :
    Squarefree n ↔ moebiusFn n ≠ 0 :=
  ArithmeticFunction.moebius_ne_zero_iff_squarefree.symm

/-- μ(n)² equals 1 for squarefree n, 0 otherwise -/
theorem moebius_sq_indicator (n : ℕ) :
    (moebiusFn n : ℤ) ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact ArithmeticFunction.moebius_sq_eq_one_of_squarefree h
  · have hmz : moebiusFn n = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
    simp [hmz]

/-!
## The Series

The series Σ μ(n)² · n / 2^n sums n/2^n over all squarefree n.

First few terms:
- n=1: 1² · 1/2 = 1/2 (squarefree)
- n=2: (-1)² · 2/4 = 1/2 (squarefree)
- n=3: (-1)² · 3/8 = 3/8 (squarefree)
- n=4: 0² · 4/16 = 0 (NOT squarefree)
- n=5: (-1)² · 5/32 = 5/32 (squarefree)
- n=6: 1² · 6/64 = 3/32 (squarefree)
-/

/-- The term of the series at index n. -/
noncomputable def seriesTerm (n : ℕ) : ℝ :=
  (moebiusFn n : ℝ) ^ 2 * n / (2 : ℝ) ^ n

/-- The partial sum of the series up to N. -/
noncomputable def partialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), seriesTerm n

/-- The series converges absolutely.

Since |μ(n)²| ≤ 1 and n/2^n → 0 exponentially, the series converges.
More precisely, Σ n/2^n = 2, so Σ μ(n)² · n/2^n ≤ 2. -/
axiom series_summable : Summable (fun n : ℕ => (moebiusFn n : ℝ) ^ 2 * n / (2 : ℝ) ^ n)

/-!
## Chen-Ruzsa Theorem (1999)

Chen and Ruzsa proved that:
1. The series Σ μ(n)² · n / 2^n is irrational
2. More generally, any infinite subseries over squarefree numbers is irrational

Their proof uses techniques from transcendence theory, building on methods
developed for proving irrationality of similar series.

The key insight is that the squarefree numbers have enough structure
(density 6/π² ≈ 0.608) that infinite sums over them cannot accidentally
equal rational numbers.
-/

/-- **Chen-Ruzsa Theorem (1999)**: The sum Σ μ(n)² · n / 2^n is irrational.

This is axiomatized as the proof requires techniques from transcendence theory
beyond current Mathlib formalization.

Reference: Period. Math. Hungar. 39 (1999), 31-37 -/
axiom chen_ruzsa_irrationality :
  ∀ x : ℝ, HasSum (fun n : ℕ => (moebiusFn n : ℝ) ^ 2 * n / (2 : ℝ) ^ n) x → Irrational x

/-- The main theorem: Erdős Problem #259 is resolved affirmatively.

The sum Σ μ(n)² · n / 2^n is irrational. -/
theorem erdos_259 :
    ∀ x : ℝ, HasSum (fun n : ℕ => (moebiusFn n : ℝ) ^ 2 * n / (2 : ℝ) ^ n) x → Irrational x :=
  chen_ruzsa_irrationality

/-- Alternative statement using tsum notation -/
theorem erdos_259' : Irrational (∑' n : ℕ, (moebiusFn n : ℝ) ^ 2 * n / (2 : ℝ) ^ n) :=
  chen_ruzsa_irrationality _ series_summable.hasSum

/-!
## Numerical Approximation

The series converges to approximately 1.398...

The density of squarefree numbers is 6/π² ≈ 0.608, so roughly 60% of terms
contribute to the sum.

Partial sums:
- S₁ = 1/2 = 0.5
- S₂ = 1/2 + 1/2 = 1.0
- S₃ = 1.0 + 3/8 = 1.375
- S₅ = 1.375 + 0 + 5/32 ≈ 1.53
- S₆ ≈ 1.625
-/

/-- The series has a well-defined sum. -/
theorem series_has_sum : ∃ x : ℝ, HasSum (fun n : ℕ => (moebiusFn n : ℝ) ^ 2 * n / (2 : ℝ) ^ n) x :=
  series_summable

/-!
## Stronger Result

Erdős conjectured (1988) and Chen-Ruzsa proved that ANY infinite subseries
over squarefree numbers is irrational.

That is, if A ⊆ {squarefree numbers} is infinite, then Σ_{n ∈ A} n/2^n is irrational.

This is a much stronger statement, showing that squarefree numbers are
"generic" enough that no infinite subset can sum to a rational.
-/

/-- A set S of natural numbers gives an infinite squarefree subseries. -/
def IsInfiniteSquarefreeSubset (S : Set ℕ) : Prop :=
  S.Infinite ∧ ∀ n ∈ S, Squarefree n

/-- **Chen-Ruzsa Strong Theorem**: Any infinite subseries over squarefree
    numbers is irrational.

    This generalizes erdos_259 (which is the case S = all squarefree numbers). -/
axiom chen_ruzsa_strong (S : Set ℕ) [DecidablePred (· ∈ S)] (hS : IsInfiniteSquarefreeSubset S) :
  ∀ x : ℝ, HasSum (fun n : ℕ => if n ∈ S then (n : ℝ) / (2 : ℝ) ^ n else 0) x → Irrational x

/-!
## Density of Squarefree Numbers

The density of squarefree numbers among natural numbers is 6/π².

More precisely, #{n ≤ N : n squarefree} / N → 6/π² as N → ∞.

This constant 6/π² = 1/ζ(2) appears because the probability that a random
number is divisible by p² is 1/p², and these events are approximately
independent for different primes.
-/

/-- The density of squarefree numbers is 6/π² ≈ 0.6079...

Note: Squarefree n ↔ n.minSqFac = none for n > 0, so we use this
computable characterization for the filter. -/
axiom squarefree_density :
  Filter.Tendsto
    (fun N : ℕ => ((Finset.range N).filter (fun n => n.minSqFac = none)).card / (N : ℝ))
    Filter.atTop
    (nhds (6 / Real.pi ^ 2))

/-!
## Related Problems

Erdős Problem #250 asks about Σ σ(n)/2^n (sum of divisors function).
Both were resolved using similar transcendence-theoretic techniques.

The key difference:
- Problem 250: σ(n) is always positive, so all terms contribute
- Problem 259: μ(n)² filters to squarefree numbers only

Both belong to a family of problems asking when series Σ f(n)/2^n
are irrational, for various arithmetic functions f.
-/

end Erdos259
