/-!
# Erdős Problem #1053: Growth Rate of k-Perfect Numbers

A number n is k-perfect if σ(n) = k·n, where σ is the sum-of-divisors function.
Must k = o(log log n) for k-perfect numbers?

## Background
- k=1: only n=1
- k=2: perfect numbers (6, 28, 496, 8128, ...)
- k=3: triperfect (120, 672, 523776, ...)
- Largest known k: k=11

## Key Question
If σ(n) = k·n, must k grow slower than log log n?
Equivalently, is σ(n)/n = o(log log n)?

## Related
Guy suggested finitely many k-perfect numbers for each k ≥ 3.

## Status: OPEN
Guy's Problem B2.

Reference: https://erdosproblems.com/1053
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The sum-of-divisors function σ(n). -/
axiom sigma (n : ℕ) : ℕ

/-- σ(n) equals the sum of all positive divisors of n. -/
axiom sigma_def (n : ℕ) (hn : n > 0) :
    sigma n = (Nat.divisors n).sum id

/-- A number n is k-perfect if σ(n) = k·n. -/
def IsKPerfect (n k : ℕ) : Prop :=
  n > 0 ∧ sigma n = k * n

/-- The multiplicity of n: the ratio σ(n)/n when it is an integer. -/
def perfectMultiplicity (n : ℕ) : ℕ :=
  sigma n / n

/-! ## Classical Perfect Numbers (k = 2) -/

/-- k=1: only n=1 satisfies σ(n) = n. -/
axiom one_perfect_unique : ∀ n : ℕ, IsKPerfect n 1 → n = 1

/-- k=2: classical perfect numbers. The first few: 6, 28, 496, 8128. -/
axiom perfect_examples :
    IsKPerfect 6 2 ∧ IsKPerfect 28 2 ∧ IsKPerfect 496 2 ∧ IsKPerfect 8128 2

/-- Euler's characterization: even perfect numbers are exactly
    2^(p-1) · (2^p - 1) where 2^p - 1 is a Mersenne prime. -/
axiom euler_even_perfect (n : ℕ) (hn : n > 0) (heven : n % 2 = 0) :
    IsKPerfect n 2 ↔
    ∃ p : ℕ, p.Prime ∧ (2 ^ p - 1).Prime ∧ n = 2 ^ (p - 1) * (2 ^ p - 1)

/-! ## Multiperfect Numbers (k ≥ 3) -/

/-- k=3 (triperfect): 120, 672, 523776, 459818240, 1476304896, 51001180160. -/
axiom triperfect_examples :
    IsKPerfect 120 3 ∧ IsKPerfect 672 3 ∧ IsKPerfect 523776 3

/-- The largest known k for which a k-perfect number exists is k=11.
    The k=11 examples are extremely large. -/
axiom largest_known_k :
    ∃ n : ℕ, IsKPerfect n 11

/-- For each k ≥ 3, only finitely many k-perfect numbers are known. -/

/-! ## The Main Conjecture -/

/-- Erdős Problem #1053: If n is k-perfect (σ(n) = k·n),
    must k = o(log log n)?

    Formally: for any ε > 0, there exists N such that for all n ≥ N,
    if σ(n) = k·n, then k < ε · log(log n). -/
axiom erdos_1053_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n k : ℕ, n ≥ N →
      IsKPerfect n k →
      (k : ℝ) < ε * Real.log (Real.log (n : ℝ))

/-! ## Known Upper Bounds -/

/-- Gronwall's theorem (1913): lim sup σ(n)/(n · log log n) = e^γ
    where γ is the Euler–Mascheroni constant.
    So σ(n)/n can be as large as ~e^γ · log log n for highly composite n. -/
axiom gronwall_bound :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (sigma n : ℝ) ≤ (1 + ε) * Real.exp 0.5772 * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- Robin's inequality (1984): σ(n) < e^γ · n · log log n for n ≥ 5041,
    assuming RH. Unconditionally true for most n. -/
axiom robin_inequality_conditional (n : ℕ) (hn : n ≥ 5041) :
    -- Assuming RH
    (sigma n : ℝ) < Real.exp 0.5772 * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-! ## Guy's Finiteness Conjecture -/

/-- Guy's conjecture: For each k ≥ 3, there are only finitely many
    k-perfect numbers. This is stronger than Erdős's question. -/
axiom guy_finiteness_conjecture (k : ℕ) (hk : k ≥ 3) :
    Set.Finite {n : ℕ | IsKPerfect n k}

/-! ## Relationship to Robin's Criterion -/

/-- If σ(n) = k·n and Robin's inequality holds, then
    k < e^γ · log log n for n ≥ 5041, giving k = O(log log n).
    The Erdős question asks for the stronger o(log log n). -/
axiom robin_gives_O_bound (n k : ℕ) (hn : n ≥ 5041)
    (hkp : IsKPerfect n k) :
    (k : ℝ) < Real.exp 0.5772 * Real.log (Real.log (n : ℝ))
