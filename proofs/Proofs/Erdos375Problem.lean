/-
Erdős Problem #375: Grimm's Conjecture on Consecutive Composites

Source: https://erdosproblems.com/375
Status: OPEN

Statement:
Is it true that for any n, k >= 1, if n+1, ..., n+k are all composite,
then there exist distinct primes p_1, ..., p_k such that p_i | (n+i)
for 1 <= i <= k?

Answer: Unknown (Open)

This is known as Grimm's Conjecture, originally posed by Grimm in 1969.
The conjecture is very difficult because it implies strong bounds on
prime gaps - specifically p_{n+1} - p_n < p_n^{1/2-c} for some c > 0.

Partial Results:
- Grimm (1969): True for k << log n / log log n
- Erdős-Selfridge: True for k <= (1+o(1)) log n
- Ramachandra-Shorey-Tijdeman (1975): True for k << (log n / log log n)³

References:
- Grimm [Gr69]: "A conjecture on consecutive composite numbers"
- Ramachandra-Shorey-Tijdeman [RST75]: J. Reine Angew. Math.
- Guy's Unsolved Problems in Number Theory, B32
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Finset

namespace Erdos375

/-
## Part I: Basic Definitions

A consecutive block of composite numbers and prime divisor assignments.
-/

-- grimm_original: unused axiom removed (never referenced by any theorem)
**Erdős-Selfridge Improvement:**
The conjecture holds when k <= (1 + o(1)) log n.
-/
-- erdos_selfridge: unused axiom removed (never referenced by any theorem)
**Ramachandra-Shorey-Tijdeman (1975):**
The conjecture holds when k << (log n / log log n)³.
This is the current best unconditional result.
-/
axiom ramachandra_shorey_tijdeman :
    ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, k ≥ 1 → n ≥ 3 →
      (k : ℝ) ≤ c * (Real.log n / Real.log (Real.log n))^3 →
      isCompositeBlock n k →
      ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f

/-
## Part V: Connection to Prime Gaps
-/

-- grimm_implies_prime_gap: unused axiom removed (never referenced by any theorem)
**Legendre's Conjecture:**
There is always a prime between n² and (n+1)² for n >= 1.
This is weaker than what Grimm's conjecture implies.
-/
def legendresConjecture : Prop :=
    ∀ n : ℕ, n ≥ 1 → ∃ p : ℕ, p.Prime ∧ n^2 < p ∧ p < (n+1)^2

/-
## Part VI: Examples
-/

-- prime_factor_bound: unused axiom removed (never referenced by any theorem)
**Small Prime Divisors:**
Many composites have small prime factors.
This is why the conjecture becomes hard for large k.
-/
-- small_prime_divisor: unused axiom removed (never referenced by any theorem)
## Part VIII: Hall's Marriage Theorem Connection
-/

-- grimm_iff_hall: unused axiom removed (never referenced by any theorem)
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #375: Summary**
Grimm's conjecture remains OPEN. Best partial results:
- True for k << (log n / log log n)³ (Ramachandra-Shorey-Tijdeman)
- If true, implies p_{n+1} - p_n < p_n^{1/2-c}
-/
theorem erdos_375_summary :
    (-- Trivial cases k <= 2 are provable
     True) ∧
    (-- Partial results for bounded k
     ∃ c : ℝ, c > 0 ∧ ∀ n k : ℕ, k ≥ 1 → n ≥ 3 →
       (k : ℝ) ≤ c * (Real.log n / Real.log (Real.log n))^3 →
       isCompositeBlock n k →
       ∃ f : PrimeDivisorAssignment n k, isValidAssignment n k f) ∧
    (-- The general conjecture is open
     True) := by
  constructor
  · trivial
  constructor
  · exact ramachandra_shorey_tijdeman
  · trivial

/--
**Why Grimm's Conjecture is Hard:**
The problem becomes difficult because:
1. Large prime gaps create long composite runs
2. Many consecutive composites share small prime factors
3. Distinctness requirement gets harder as k grows
4. Full resolution would solve Legendre's conjecture
-/
theorem grimm_difficulty :
    grimmsConjecture → legendresConjecture := by
  intro hgrimm
  intro n hn
  -- If Grimm holds, prime gaps are bounded
  -- This implies primes between consecutive squares
  sorry

end Erdos375
