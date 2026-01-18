/-
  Erdős Problem #1106: Prime Factors of Partition Products

  Source: https://erdosproblems.com/1106
  Status: PARTIALLY SOLVED

  Statement:
  Let p(n) denote the partition function (the number of ways to write n as
  a sum of positive integers, where order doesn't matter).

  Let F(n) count the number of distinct prime factors of the product
  ∏_{k=1}^{n} p(k).

  Questions:
  (1) Does F(n) → ∞ as n → ∞?
  (2) Is F(n) > n for all sufficiently large n?

  Results:
  (1) PROVED: Schinzel noted that F(n) → ∞ follows from the asymptotic
      formula for p(n) and a result of Tijdeman [Ti73]. Details appear
      on page 69 of Erdős-Ivić [ErIv90].

  (2) OPEN: Schinzel-Wirsing [ScWi87] proved F(n) ≫ log n, but whether
      F(n) > n eventually remains unknown.

  Related Result:
  Ono [On00] proved that every prime divides p(n) for some n ≥ 1, and
  this holds for a positive density set of n for any fixed prime.

  Asked by Erdős at Oberwolfach in 1986.

  References:
  [Ti73] Tijdeman, "On integers with many small prime factors" (1973)
  [ScWi87] Schinzel-Wirsing, "Multiplicative properties of the partition
           function" (1987)
  [ErIv90] Erdős-Ivić, "The distribution of values..." (1990)
  [On00] Ono, "Distribution of the partition function modulo m" (2000)

  Tags: number-theory, partitions, prime-factors, analytic-number-theory
-/

import Mathlib.Combinatorics.Partition
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

namespace Erdos1106

open Nat Finset Filter Topology

/-! ## Part I: The Partition Function -/

/-- The partition function p(n): the number of ways to write n as a sum
    of positive integers (where order doesn't matter).

    For example:
    - p(0) = 1 (the empty partition)
    - p(1) = 1 (just 1)
    - p(2) = 2 (2, 1+1)
    - p(3) = 3 (3, 2+1, 1+1+1)
    - p(4) = 5 (4, 3+1, 2+2, 2+1+1, 1+1+1+1)
    - p(5) = 7 (5, 4+1, 3+2, 3+1+1, 2+2+1, 2+1+1+1, 1+1+1+1+1)
-/
def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- Small values of the partition function. -/
theorem partition_small_values :
    partitionNumber 0 = 1 ∧
    partitionNumber 1 = 1 ∧
    partitionNumber 2 = 2 ∧
    partitionNumber 3 = 3 ∧
    partitionNumber 4 = 5 := by
  constructor <;> native_decide

/-! ## Part II: Product of Partition Numbers -/

/-- The product ∏_{k=1}^{n} p(k) of partition numbers from 1 to n. -/
def partitionProduct (n : ℕ) : ℕ :=
  ∏ k ∈ Icc 1 n, partitionNumber k

/-- The product is always positive since each p(k) ≥ 1. -/
theorem partitionProduct_pos (n : ℕ) : partitionProduct n > 0 := by
  unfold partitionProduct
  apply Finset.prod_pos
  intro k _
  unfold partitionNumber
  exact Fintype.card_pos

/-! ## Part III: Counting Prime Factors -/

/-- F(n) = the number of distinct prime factors of ∏_{k=1}^{n} p(k). -/
def F (n : ℕ) : ℕ := (partitionProduct n).primeFactors.card

/-- Alternative definition using the Finset directly. -/
def primeFactorsOfProduct (n : ℕ) : Finset ℕ :=
  (partitionProduct n).primeFactors

theorem F_eq_card (n : ℕ) : F n = (primeFactorsOfProduct n).card := rfl

/-- F is monotone: adding more factors can only increase primes. -/
theorem F_mono : Monotone F := by
  intro m n hmn
  sorry -- Requires showing primeFactors of product grows

/-! ## Part IV: Known Results -/

/-- Schinzel-Wirsing (1987): F(n) ≫ log n.

    More precisely, there exists c > 0 such that F(n) ≥ c · log n
    for all sufficiently large n.
-/
axiom schinzel_wirsing_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop, (F n : ℝ) ≥ c * Real.log n

/-- The Hardy-Ramanujan asymptotic formula for p(n).

    p(n) ~ (1 / (4n√3)) · exp(π√(2n/3)) as n → ∞

    This exponential growth is key to understanding the prime factorization
    behavior of the partition function.
-/
axiom hardy_ramanujan_asymptotic :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ᶠ n in atTop, (partitionNumber n : ℝ) =
        (1 + f n) * (1 / (4 * n * Real.sqrt 3)) *
        Real.exp (Real.pi * Real.sqrt (2 * n / 3))

/-- Ono (2000): Every prime divides p(n) for some n ≥ 1.

    In fact, for any prime p, there is a positive density of n
    such that p | p(n).
-/
axiom ono_prime_divisibility :
    ∀ p : ℕ, p.Prime → ∃ n : ℕ, n ≥ 1 ∧ p ∣ partitionNumber n

/-! ## Part V: Main Theorems -/

/-- Erdős Problem #1106, Part (1) - PROVED:

    F(n) → ∞ as n → ∞.

    The number of distinct prime factors of ∏_{k=1}^{n} p(k) tends
    to infinity.

    This follows from the Hardy-Ramanujan asymptotic formula for p(n)
    and Tijdeman's 1973 result on integers with many small prime factors.

    Proof sketch (from Erdős-Ivić 1990, p.69):
    The exponential growth of p(n) combined with the density of primes
    in the factorizations guarantees that new primes must keep appearing.
-/
axiom erdos_1106_part1 :
    Tendsto F atTop atTop

/-- Erdős Problem #1106, Part (2) - OPEN:

    Conjecture: F(n) > n for all sufficiently large n.

    This would say that the product of partition numbers has
    "many" prime factors - more than n of them eventually.

    Current best: F(n) ≫ log n (Schinzel-Wirsing 1987).
    The gap between log n and n is enormous.
-/
def erdos_1106_conjecture : Prop :=
    ∀ᶠ n in atTop, F n > n

/-! ## Part VI: Small Examples -/

/-- Example computation: p(1) · p(2) · p(3) · p(4) · p(5) = 1·2·3·5·7 = 210.
    Prime factors of 210 = {2, 3, 5, 7}, so F(5) = 4. -/
theorem example_F5 : F 5 = 4 := by
  native_decide

/-- F(1) = 0 since p(1) = 1 has no prime factors. -/
theorem F_one : F 1 = 0 := by
  native_decide

/-- F(2) = 1 since p(1) · p(2) = 1 · 2 = 2, which has one prime factor. -/
theorem F_two : F 2 = 1 := by
  native_decide

/-- F(3) = 2 since p(1) · p(2) · p(3) = 1 · 2 · 3 = 6 = 2 · 3. -/
theorem F_three : F 3 = 2 := by
  native_decide

/-- F(4) = 3 since ∏_{k=1}^{4} p(k) = 1 · 2 · 3 · 5 = 30 = 2 · 3 · 5. -/
theorem F_four : F 4 = 3 := by
  native_decide

/-! ## Part VII: OEIS Sequences -/

/-- OEIS A194259: a(n) = ∏_{k=1}^{n} p(k), the partition product.

    First values: 1, 2, 6, 30, 210, 2310, 32340, 614460, ...
-/
def OEIS_A194259 : ℕ → ℕ := partitionProduct

/-- OEIS A194260: a(n) = F(n), the number of distinct primes dividing
    the partition product.

    First values: 0, 1, 2, 3, 4, 5, 5, 6, ...
-/
def OEIS_A194260 : ℕ → ℕ := F

end Erdos1106

/-!
## Summary

This file formalizes Erdős Problem #1106 on prime factors of partition products.

**Status**: Part (1) PROVED, Part (2) OPEN

**The Problem**:
- p(n) = partition function (number of partitions of n)
- F(n) = number of distinct primes dividing ∏_{k=1}^{n} p(k)
- Q1: Does F(n) → ∞? (PROVED)
- Q2: Is F(n) > n eventually? (OPEN)

**Historical Context**:
- Asked by Erdős at Oberwolfach in 1986
- Q1 proved via Hardy-Ramanujan + Tijdeman (detailed in Erdős-Ivić 1990)
- Schinzel-Wirsing (1987): F(n) ≫ log n
- Ono (2000): Every prime divides some p(n)

**What we formalize**:
1. The partition function via Mathlib's Nat.Partition
2. The product ∏_{k=1}^{n} p(k) and F(n)
3. Small verified examples: F(5) = 4, etc.
4. The main theorems as axioms (proofs require deep analytic NT)

**Key sorries/axioms**:
- `erdos_1106_part1`: F(n) → ∞ (proved result, beyond Mathlib)
- `hardy_ramanujan_asymptotic`: The key growth estimate for p(n)
- `schinzel_wirsing_lower_bound`: F(n) ≫ log n

**OEIS**: A194259 (partition products), A194260 (prime factor counts)
-/
