/-
Erdős Problem #684: Smooth Parts of Binomial Coefficients

**Problem Statement (OPEN)**

For binomial coefficient C(n,k), decompose C(n,k) = u·v where:
- u contains only prime factors from [2, k]
- v contains only prime factors from (k, n]

Let f(n) be the smallest k such that u > n².

Question: What are the bounds on f(n)?

**Background:**
- The "smooth part" u consists of primes ≤ k
- The "rough part" v consists of primes in (k, n]
- We ask how small k can be while still having a large smooth part

**Known Results:**
- Mahler: For any ε > 0, u ≤ n^{1+ε} for large n (ineffective)
- Tang & ChatGPT: f(n) ≤ n^{30/43+o(1)}
- Under RH: f(n) ≤ n^{2/3+o(1)} conjectured
- Heuristic: f(n) ~ 2 log n for most n

**Status:** OPEN

**Reference:** [Er79d], OEIS A392019

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos684

/-!
# Part 1: Smooth and Rough Parts of Binomial Coefficients

Decompose C(n,k) into parts based on prime factor ranges.
-/

-- The k-smooth part of a number: product of prime power factors with p ≤ k
noncomputable def smoothPart (k m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
    p ^ (m.factorization p)

-- The k-rough part: product of prime power factors with p > k
noncomputable def roughPart (k m : ℕ) : ℕ :=
  m / smoothPart k m

-- Decomposition theorem
theorem smooth_rough_decomposition (k m : ℕ) (hm : m > 0) :
    m = smoothPart k m * roughPart k m := by
  simp only [roughPart]
  sorry  -- Requires showing smooth divides m

-- For binomial coefficient, decompose by factor range
noncomputable def binomialSmoothPart (n k : ℕ) : ℕ :=
  smoothPart k (Nat.choose n k)

noncomputable def binomialRoughPart (n k : ℕ) : ℕ :=
  roughPart k (Nat.choose n k)

/-!
# Part 2: The Function f(n)

f(n) is the smallest k such that the smooth part exceeds n².
-/

-- f(n) = min {k : smoothPart(C(n,k)) > n²}
noncomputable def f (n : ℕ) : ℕ :=
  Nat.find ⟨n, by sorry⟩  -- Existence needs proof

-- Property of f: at k = f(n), smooth part > n²
axiom f_property (n : ℕ) (hn : n ≥ 2) :
    binomialSmoothPart n (f n) > n^2

-- Below f(n), smooth part ≤ n²
axiom below_f_small (n k : ℕ) (hn : n ≥ 2) (hk : k < f n) :
    binomialSmoothPart n k ≤ n^2

/-!
# Part 3: Mahler's Classical Result

The smooth part is bounded by n^{1+ε} for large n.
-/

-- Mahler's theorem (ineffective): smooth part bounded
-- For any ε > 0, ∃ N such that ∀ n ≥ N, k ≤ n, smoothPart(C(n,k)) ≤ n^{1+ε}
axiom mahler_ineffective : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ n,
    (binomialSmoothPart n k : ℝ) ≤ n^(1 + ε)

-- Mahler implies f(n) → ∞
theorem f_tendsto_infty_weak : ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n > C := by
  intro C
  sorry  -- Follows from Mahler

/-!
# Part 4: Modern Bounds

Recent results by Tang & ChatGPT on explicit bounds for f(n).
-/

-- Tang-ChatGPT bound: f(n) ≤ n^{30/43 + o(1)}
-- The exponent 30/43 ≈ 0.698
def tang_exponent : ℝ := 30 / 43

axiom tang_bound : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (f n : ℝ) ≤ n^(tang_exponent + ε)

-- Under Riemann Hypothesis: f(n) ≤ n^{2/3 + o(1)}
def rh_exponent : ℝ := 2 / 3

axiom rh_conditional_bound : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    -- Assuming RH
    (f n : ℝ) ≤ n^(rh_exponent + ε)

/-!
# Part 5: Heuristic Conjectures

The heuristic suggests f(n) ~ 2 log n for most n.
-/

-- Sothanaphan-ChatGPT heuristic: f(n) ~ 2 log n for "most" n
-- This is much smaller than the proven bounds!
def heuristic_bound (n : ℕ) : ℝ := 2 * Real.log n

-- The heuristic (not proven)
axiom heuristic_conjecture : ∀ ε : ℝ, ε > 0 →
    -- For density 1 set of n
    ∃ S : Set ℕ, (∀ N, (↑(Finset.filter (· ∈ S) (Finset.range N)).card / N : ℝ) > 1 - ε) ∧
    (∀ n ∈ S, |((f n : ℝ) - heuristic_bound n) / heuristic_bound n| < ε)

/-!
# Part 6: Structure of Smooth Part

The smooth part is determined by primes in [2, k] dividing C(n,k).
-/

-- Prime power in C(n,k) via Kummer's theorem
-- v_p(C(n,k)) = (carries in base-p addition of k + (n-k)) / (p-1)
-- Actually: v_p(C(n,k)) = number of carries when adding k + (n-k) in base p

-- Legendre's formula for factorial
noncomputable def legendreExponent (n p : ℕ) (hp : p.Prime) : ℕ :=
  ∑ i ∈ Finset.range n, n / p^(i + 1)

-- Kummer's theorem
axiom kummer_theorem (n k p : ℕ) (hp : p.Prime) (hk : k ≤ n) :
    (Nat.choose n k).factorization p =
    (legendreExponent n p hp - legendreExponent k p hp - legendreExponent (n - k) p hp)

/-!
# Part 7: Special Cases

Examine f(n) for small n and special values.
-/

-- f(n) ≥ 2 for n ≥ 4 (otherwise smooth part too small)
axiom f_lower_bound : ∀ n ≥ 4, f n ≥ 2

-- For prime n, behavior may differ
-- C(p, k) for prime p has special structure
theorem prime_binomial_structure (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ p - 1) :
    p ∣ Nat.choose p k := by
  exact Nat.Prime.dvd_choose hp hk.1 hk.2

/-!
# Part 8: The Generalized Problem

Bounds on f(n, k) for the smallest k such that smooth part exceeds n².
-/

-- Generalized: f(n, j) = smallest k ≥ j such that smooth part > n²
noncomputable def fGeneral (n j : ℕ) : ℕ :=
  Nat.find ⟨n, by sorry⟩  -- Needs existence proof

-- Connection to original: f(n) = fGeneral(n, 0)
theorem f_is_fGeneral_0 (n : ℕ) : f n = fGeneral n 0 := by
  sorry  -- Definition equivalence

/-!
# Part 9: OEIS Sequence

The sequence f(n) is recorded in OEIS A392019.
-/

-- OEIS A392019: values of f(n)
-- First few terms would need computation

def oeis_reference : String := "A392019"

/-!
# Part 10: Problem Status

The problem remains OPEN. Best known bounds leave a large gap.
-/

-- The problem is open
def erdos_684_status : String := "OPEN"

-- Main formal statement
theorem erdos_684_statement :
    ∀ n ≥ 2, ∃ k ≤ n, binomialSmoothPart n k > n^2 := by
  intro n hn
  use f n
  constructor
  · sorry  -- f(n) ≤ n
  · exact f_property n hn

-- Known bounds summary
-- Lower: f(n) ≥ (some function)
-- Upper: f(n) ≤ n^{30/43 + o(1)}
-- Heuristic: f(n) ~ 2 log n

/-!
# Summary

**Problem:** Find bounds on f(n) = min k such that k-smooth part of C(n,k) > n².

**Known:**
- Mahler: smooth part ≤ n^{1+ε} (ineffective)
- Tang-ChatGPT: f(n) ≤ n^{30/43 + o(1)}
- RH conditional: f(n) ≤ n^{2/3 + o(1)}

**Heuristic:** f(n) ~ 2 log n for most n

**Gap:** Huge gap between proven bounds and heuristic!
-/

end Erdos684
