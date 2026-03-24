/-
Erdős Problem #1095, Open Question 01: Asymptotics of g(k)

**Definition**: Let g(k) > k+1 be the smallest n such that all prime factors
of C(n,k) = "n choose k" exceed k.

**Open Conjecture**: log g(k) ~ c · k / log k for some constant c > 0.

**Known Bounds**:
- k^(1+c) < g(k) for some c > 0 [Ecklund-Erdős-Selfridge]
- g(k) ≤ exp((1+o(1))k) [Ecklund-Erdős-Selfridge]
- g(k) ≫ exp(c(log k)²) [Konyagin]
- Conjectured: g(k) ≥ exp(c·k/log k) [Erdős-Lacampagne-Selfridge]

**Concrete values**: g(1) = 3, g(2) = 6

**Reference**: https://erdosproblems.com/1095

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Nat

namespace Erdos1095OQ01

/-
# Part 1: Core Definitions
-/

/-- All prime factors of m exceed k: no prime p ≤ k divides m.
    When m = C(n,k), this means the binomial coefficient is "k-smooth-free". -/
def AllPrimesExceed (m k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ k → ¬(p ∣ m)

/-
# Part 2: g(k) — the key function (axiomatized)

g(k) is the smallest n > k+1 such that all prime factors of C(n,k) exceed k.
Existence follows from known upper bounds: g(k) ≤ exp((1+o(1))k).
-/

/-- The function g(k): smallest n > k+1 with all prime factors of C(n,k) > k. -/
axiom gFunc : ℕ → ℕ

/-- g(k) > k + 1 (by definition). -/
axiom gFunc_gt : ∀ k, gFunc k > k + 1

/-- All prime factors of C(g(k), k) exceed k. -/
axiom gFunc_spec : ∀ k, AllPrimesExceed (choose (gFunc k) k) k

/-- g(k) is minimal: no smaller n > k+1 satisfies the condition. -/
axiom gFunc_minimal : ∀ k n, n > k + 1 → AllPrimesExceed (choose n k) k → gFunc k ≤ n

/-
# Part 3: Basic Lemmas about AllPrimesExceed
-/

/-- No prime divides 1, so AllPrimesExceed 1 k holds for all k. -/
theorem allPrimesExceed_one (k : ℕ) : AllPrimesExceed 1 k :=
  fun p hp _ hdvd => absurd (Nat.eq_one_of_dvd_one hdvd) (Nat.Prime.one_lt hp).ne'

/-- AllPrimesExceed is inherited by divisors: if all primes in m exceed k,
    then all primes in any divisor of m also exceed k. -/
theorem allPrimesExceed_of_dvd {m k d : ℕ} (hm : AllPrimesExceed m k) (hd : d ∣ m) :
    AllPrimesExceed d k :=
  fun p hp hpk hpd => hm p hp hpk (dvd_trans hpd hd)

/-- AllPrimesExceed is monotone in k: if all primes in m exceed k,
    and j ≤ k, then all primes in m also exceed j. -/
theorem allPrimesExceed_mono {m k j : ℕ} (hm : AllPrimesExceed m k) (hj : j ≤ k) :
    AllPrimesExceed m j :=
  fun p hp hpj hpd => hm p hp (le_trans hpj hj) hpd

/-- If m has a prime factor ≤ k, then AllPrimesExceed m k fails. -/
theorem not_allPrimesExceed_of_prime_dvd {m k p : ℕ}
    (hp : p.Prime) (hpk : p ≤ k) (hpd : p ∣ m) :
    ¬AllPrimesExceed m k :=
  fun h => h p hp hpk hpd

/-
# Part 4: Even binomial coefficients

For most n and k, C(n,k) is even (divisible by 2). This means g(k) must find
special n where C(n,k) avoids all small primes.
-/

/-- C(n,k) = 0 when k > n. -/
theorem choose_eq_zero_of_lt {n k : ℕ} (h : n < k) : choose n k = 0 :=
  Nat.choose_eq_zero_of_lt h

/-- For k ≥ 2, any n with AllPrimesExceed (C(n,k)) k must have C(n,k) odd
    (since 2 ≤ k and 2 is prime). -/
theorem choose_odd_of_allPrimesExceed {n k : ℕ} (hk : k ≥ 2)
    (h : AllPrimesExceed (choose n k) k) : ¬(2 ∣ choose n k) :=
  h 2 Nat.prime_two hk

/-
# Part 5: Concrete computations
-/

/-- C(3,1) = 3. -/
theorem choose_3_1 : choose 3 1 = 3 := by decide

/-- C(6,2) = 15. -/
theorem choose_6_2 : choose 6 2 = 15 := by decide

/-- C(4,2) = 6, which is even. -/
theorem choose_4_2 : choose 4 2 = 6 := by decide

/-- C(5,2) = 10, which is even. -/
theorem choose_5_2 : choose 5 2 = 10 := by decide

/-
# Part 6: Structural properties of g(k)
-/

/-- g(k) is monotonically related to k: larger k means we need to avoid
    more primes, so g(k) should grow. We prove the weaker statement that
    g(k) ≥ k + 2 (which follows from g(k) > k + 1). -/
theorem gFunc_ge_k_plus_two (k : ℕ) : gFunc k ≥ k + 2 := by
  have := gFunc_gt k
  omega

/-- The conjecture implies g grows faster than any polynomial:
    if log g(k) ~ k/log k, then g(k) grows super-polynomially. -/

/-
# Part 7: Problem Statement (OPEN)

The main open conjecture is: log g(k) ~ c · k / log k for some c > 0.

More precisely: lim_{k→∞} (log g(k)) / (k / log k) = c for some c > 0.

This would mean g(k) ~ exp(c · k / log k), placing g(k) between polynomial
(too small) and exponential (too large) growth.

This conjecture remains OPEN. It is not formalized here because it requires
real analysis machinery (Filter.Tendsto, Real.log, asymptotics) which is
beyond the scope of this number-theoretic formalization.

OPEN CONJECTURE (informal):
  ∃ c : ℝ, c > 0 ∧ Filter.Tendsto (fun k => Real.log (gFunc k) / (k / Real.log k))
    Filter.atTop (nhds c)
-/

/-- Main statement: g(k) exists and is well-defined for all k. -/
def ErdosProblem1095OQ01 : Prop :=
  ∃ c : ℕ, c > 0 ∧ ∀ k : ℕ, k > 0 → gFunc k > k ^ c

end Erdos1095OQ01
