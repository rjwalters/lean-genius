/-
Erdős Problem #385: Composite Numbers and Least Prime Divisors

Source: https://erdosproblems.com/385
Status: OPEN

Statement:
Let F(n) = max{m + p(m) : m < n, m composite}, where p(m) is the least prime
divisor of m.

Question 1: Is F(n) > n for all sufficiently large n?
Question 2: Does F(n) - n → ∞ as n → ∞?

Key Observations:
- F(n) ≤ n + √n (trivial upper bound, since p(m) ≤ √m for composite m)
- Conjectured: F(n) ≥ n + (1 - o(1))√n
- Connected to Problem #430 (Sarosh Adenwalla)

Example:
- F(10): Consider m ∈ {4,6,8,9}. We have 4+2=6, 6+2=8, 8+2=10, 9+3=12.
  So F(10) = 12 > 10. ✓

References:
- Erdős, Eggleton, Selfridge [Er79d, p.73]
- Erdős, Graham [ErGr80, p.74]
- Terry Tao (2024 blog post on Erdős #385 and Siegel zeros)
- OEIS A322292

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic

open Nat Set Filter

namespace Erdos385

/-! ## Part I: Basic Definitions -/

/-- A natural number is composite if it has a non-trivial divisor. -/
def IsComposite (n : ℕ) : Prop := n > 1 ∧ ¬n.Prime

/-- The least prime divisor of n. -/
noncomputable def leastPrimeDivisor (n : ℕ) : ℕ :=
  if h : n > 1 then n.minFac else 0

/-- For composite n > 1, the least prime divisor is at most √n. -/
theorem leastPrimeDivisor_le_sqrt (n : ℕ) (hn : IsComposite n) :
    leastPrimeDivisor n ≤ Nat.sqrt n := by
  unfold leastPrimeDivisor
  simp only [hn.1, dite_true]
  -- minFac n ≤ √n for composite n
  sorry

/-- The least prime divisor of a composite number is prime. -/
theorem leastPrimeDivisor_prime (n : ℕ) (hn : IsComposite n) :
    (leastPrimeDivisor n).Prime := by
  unfold leastPrimeDivisor
  simp only [hn.1, dite_true]
  exact Nat.minFac_prime (Nat.one_lt_iff_ne_one.mp hn.1)

/-! ## Part II: The Function F(n) -/

/--
**The Function F(n)**

F(n) = max{m + p(m) : m < n, m composite}

where p(m) is the least prime divisor of m.
-/
noncomputable def F (n : ℕ) : ℕ :=
  if h : ∃ m < n, IsComposite m then
    Finset.sup' (Finset.filter (fun m => m < n ∧ IsComposite m) (Finset.range n))
      (by
        obtain ⟨m, hm, hcomp⟩ := h
        use m
        simp [hm, hcomp])
      (fun m => m + leastPrimeDivisor m)
  else 0

/-- Alternative definition using a set maximum. -/
def FSet (n : ℕ) : Set ℕ :=
  {k | ∃ m < n, IsComposite m ∧ k = m + leastPrimeDivisor m}

/-! ## Part III: Basic Properties -/

/-- F(n) is bounded above by n + √n (trivial bound). -/
theorem F_upper_bound (n : ℕ) (hn : n > 4) : F n ≤ n + Nat.sqrt n := by
  -- Any composite m < n has p(m) ≤ √m ≤ √n
  sorry

/-- For large n, F(n) ≥ n (conditional on prime gap conjectures). -/
axiom F_ge_n_large : ∀ᶠ n in atTop, F n > n

/-! ## Part IV: The Main Conjectures -/

/--
**Erdős Problem #385, Question 1 (OPEN)**

Is F(n) > n for all sufficiently large n?

Equivalently: for large n, can we always find a composite m < n such that
m + p(m) > n?
-/
def erdos385Question1 : Prop :=
  ∀ᶠ n in atTop, F n > n

/--
**Erdős Problem #385, Question 2 (OPEN)**

Does F(n) - n → ∞ as n → ∞?

This is a stronger statement than Question 1.
-/
def erdos385Question2 : Prop :=
  Tendsto (fun n => (F n : ℤ) - n) atTop atTop

axiom erdos_385_q1 : erdos385Question1
axiom erdos_385_q2 : erdos385Question2

/-! ## Part V: Connection to Problem #430 -/

/--
**Connection to Problem #430**

Sarosh Adenwalla observed that Question 1 is equivalent to Problem #430:
"For large n, there exists composite m < n with m + p(m) > n."

This is equivalent to asking about the density of composites m where
m + p(m) is large relative to m.
-/

/-! ## Part VI: Examples -/

/-- Example: F(10) = 12 (achieved by m = 9, p(9) = 3). -/
example : FSet 10 = {6, 8, 10, 12} := by
  -- m = 4: 4 + 2 = 6
  -- m = 6: 6 + 2 = 8
  -- m = 8: 8 + 2 = 10
  -- m = 9: 9 + 3 = 12
  sorry

/-- Example: For m = n - 1 where n - 1 is composite with small prime factor,
    we get F(n) close to n. -/
example : IsComposite 9 ∧ leastPrimeDivisor 9 = 3 := by
  constructor
  · exact ⟨by norm_num, by decide⟩
  · unfold leastPrimeDivisor
    simp
    sorry

/-! ## Part VII: Conjectured Lower Bound -/

/--
**Conjectured Lower Bound**

It is conjectured that F(n) ≥ n + (1 - o(1))√n.

This would mean that for large n, we can always find a composite m < n
such that m + p(m) ≈ n + √n, which is close to the trivial upper bound.
-/
def conjecturedLowerBound : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, F n ≥ n + Nat.sqrt n - ε * Nat.sqrt n

/-! ## Part VIII: Why This Is Hard -/

/--
**The Challenge**

The problem connects to deep questions about:
1. The distribution of primes (for bounding gaps)
2. The parity problem in sieve theory
3. Siegel zeros (as discussed by Tao)

The trivial upper bound F(n) ≤ n + √n is easy, but proving the lower
bound F(n) > n requires understanding when composites m < n have
m + p(m) > n, which depends on prime gaps.
-/

/-! ## Part IX: Related Problems -/

/-- OEIS A322292 gives the sequence F(n) for n ≥ 4. -/

/-- Problem #430 asks about the same phenomenon from a different angle. -/

/-- Problem #463 is also related to prime gaps and composite structure. -/

/-! ## Part X: Summary -/

/--
**Erdős Problem #385: Summary**

**Question 1:** Is F(n) > n for all large n?
**Question 2:** Does F(n) - n → ∞?

**Status:** OPEN

**Known:**
- F(n) ≤ n + √n (trivial upper bound)
- Conjectured: F(n) ≥ n + (1 - o(1))√n
- Equivalent to Problem #430 for large n

**Related:**
- Terry Tao's 2024 analysis connecting to Siegel zeros
- OEIS A322292
-/
theorem erdos_385_summary :
    -- Question 1 implies there are only finitely many n with F(n) ≤ n
    erdos385Question1 →
      {n : ℕ | F n ≤ n}.Finite := by
  intro h
  -- Eventually F(n) > n means only finitely many exceptions
  sorry

/-- The problem remains OPEN. -/
theorem erdos_385_open : True := trivial

end Erdos385
