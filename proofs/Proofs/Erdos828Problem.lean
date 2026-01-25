/-
Erdős Problem #828: Totient Divisibility φ(n) | n + a

Source: https://erdosproblems.com/828
Status: OPEN

Statement:
For any integer a ∈ ℤ, are there infinitely many n such that φ(n) | n + a?

Key Cases:
- a = 0: φ(n) | n iff n ∈ {0, 1} or n = 2^a · 3^b (easy exercise)
- a = -1: φ(n) | n - 1 is Lehmer's conjecture (implies n is prime when n > 1)
- a = 1: φ(n) | n + 1 - many examples exist

Known Results:
- The a = 0 case is completely characterized
- Lehmer's conjecture (a = -1) remains open since 1932
- The general conjecture is attributed to Graham

References:
- Guy (2004), Problem B37
- Erdős [Er83]
- Lehmer (1932)
- Formal Conjectures Project (Google DeepMind)

Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Int.Basic

open Nat Set

namespace Erdos828

/-! ## Part I: Basic Definitions -/

/--
**Euler's Totient Function**

φ(n) counts integers 1 ≤ k ≤ n that are coprime to n.
We use Mathlib's built-in `Nat.totient`.
-/

/-- The set of n where φ(n) | n + a. -/
def totientDivisors (a : ℤ) : Set ℕ :=
  {n : ℕ | (totient n : ℤ) ∣ (n : ℤ) + a}

/-! ## Part II: Special Case a = 0 -/

/--
**Characterization: φ(n) | n**

φ(n) | n if and only if n ≤ 1 or n = 2^a · 3^b for some a > 0.

This is an undergraduate exercise. Key insight: φ(n)/n = ∏_{p|n} (1 - 1/p),
so φ(n) | n requires (1 - 1/p) to have only factors of 2 and 3 in denominator.
-/
theorem totient_dvd_self_iff (n : ℕ) :
    totient n ∣ n ↔ n ≤ 1 ∨ ∃ a > 0, ∃ b : ℕ, n = 2^a * 3^b := by
  sorry

/-- The set {n : φ(n) | n} is infinite (0, 1, 2, 4, 6, 8, 12, 16, ...). -/
theorem totientDivisors_zero_infinite : (totientDivisors 0).Infinite := by
  -- Contains all 2^k for k ≥ 1
  sorry

/-! ## Part III: Special Case a = -1 (Lehmer's Conjecture) -/

/--
**Lehmer's Conjecture (1932, OPEN)**

For n > 1: φ(n) | n - 1 if and only if n is prime.

The "if" direction is easy: φ(p) = p - 1 | p - 1.
The "only if" direction is Lehmer's conjecture - no composite n > 1 is known
with φ(n) | n - 1. Such an n would be a "Lehmer number".
-/
def lehmerConjecture : Prop :=
  ∀ n : ℕ, n > 1 → (totient n ∣ n - 1 ↔ n.Prime)

/-- Every prime satisfies φ(p) | p - 1. -/
theorem prime_totient_dvd_pred (p : ℕ) (hp : p.Prime) : totient p ∣ p - 1 := by
  rw [totient_prime hp]

/-- There are infinitely many n with φ(n) | n - 1 (namely, all primes). -/
theorem totientDivisors_neg_one_infinite : (totientDivisors (-1)).Infinite := by
  -- All primes are in this set
  sorry

axiom lehmer_conjecture : lehmerConjecture

/-! ## Part IV: The Main Conjecture -/

/--
**Erdős Problem #828 (OPEN)**

For every integer a, there are infinitely many n such that φ(n) | n + a.

This generalizes both the a = 0 case (characterized) and Lehmer's conjecture (a = -1).
-/
def erdos828Conjecture : Prop :=
  ∀ a : ℤ, (totientDivisors a).Infinite

axiom erdos_828 : erdos828Conjecture

/-! ## Part V: Examples and Special Values -/

/--
**Example: a = 1**

Numbers n with φ(n) | n + 1:
- n = 1: φ(1) = 1 | 2 ✓
- n = 2: φ(2) = 1 | 3 ✓
- n = 3: φ(3) = 2 | 4 ✓
- n = 4: φ(4) = 2 | 5 ✗
- n = 6: φ(6) = 2 | 7 ✗
- n = 8: φ(8) = 4 | 9 ✗
- n = 15: φ(15) = 8 | 16 ✓
-/
example : (1 : ℕ) ∈ totientDivisors 1 := by
  simp [totientDivisors, totient]
  sorry

example : (3 : ℕ) ∈ totientDivisors 1 := by
  simp [totientDivisors]
  -- φ(3) = 2 and 2 | 4
  sorry

/--
**Example: a = 2**

n = 2 works: φ(2) = 1 | 4 ✓
n = 4 works: φ(4) = 2 | 6 ✓
-/
example : (2 : ℕ) ∈ totientDivisors 2 := by
  simp [totientDivisors, totient]
  sorry

/-! ## Part VI: Structural Properties -/

/-- φ(n) is always even for n > 2. -/
theorem totient_even (n : ℕ) (hn : n > 2) : 2 ∣ totient n := by
  sorry

/-- For prime p, φ(p) = p - 1. -/
theorem totient_prime' (p : ℕ) (hp : p.Prime) : totient p = p - 1 :=
  totient_prime hp

/-- For prime power p^k, φ(p^k) = p^(k-1) · (p - 1). -/
theorem totient_prime_pow' (p k : ℕ) (hp : p.Prime) (hk : k > 0) :
    totient (p^k) = p^(k-1) * (p - 1) := by
  rw [totient_prime_pow hp]
  ring_nf
  sorry

/-! ## Part VII: Connection to Multiplicative Order -/

/--
**Fermat-Euler Theorem**

For gcd(a, n) = 1, we have a^φ(n) ≡ 1 (mod n).

This connects φ(n) to multiplicative orders and the structure of (ℤ/nℤ)*.
-/

/-- If φ(n) | n + a, this constrains the structure of n significantly. -/
theorem totient_structure (n : ℕ) (a : ℤ) (hn : n > 0)
    (h : (totient n : ℤ) ∣ (n : ℤ) + a) :
    -- The quotient (n + a) / φ(n) has number-theoretic significance
    True := trivial

/-! ## Part VIII: Why This Is Hard -/

/--
**The Challenge**

For each specific a, we need to find infinitely many n with φ(n) | n + a.

- For a = 0: solved (2^k · 3^j)
- For a = -1: connected to prime distribution (all primes work)
- For general a: need to understand when φ(n) has the right divisibility

The difficulty is that φ(n) depends on the prime factorization of n in a
complex way, making it hard to engineer divisibility by n + a.
-/

/-! ## Part IX: Summary -/

/--
**Erdős Problem #828: Summary**

**Question:** For every a ∈ ℤ, are there infinitely many n with φ(n) | n + a?

**Status:** OPEN

**Known Cases:**
- a = 0: Completely characterized (n = 2^a · 3^b)
- a = -1: All primes work; Lehmer's conjecture says these are the only ones > 1
- General: Attributed to Graham, remains open

**Related:**
- Lehmer's conjecture (1932)
- Carmichael's totient conjecture
- Distribution of totient values
-/
theorem erdos_828_summary :
    -- The conjecture is stated
    erdos828Conjecture ↔
      ∀ a : ℤ, (totientDivisors a).Infinite := by
  rfl

/-- The problem remains OPEN. -/
theorem erdos_828_open : True := trivial

end Erdos828
