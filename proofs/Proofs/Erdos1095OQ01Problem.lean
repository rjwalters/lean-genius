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

import Mathlib

open Nat Filter

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

/-- Existence: for each k, there exists n > k+1 with all prime factors
    of C(n,k) exceeding k. Follows from the Ecklund-Erdős-Selfridge
    upper bound: g(k) ≤ exp((1+o(1))k). -/
axiom gFunc_exists (k : ℕ) :
    ∃ n, n > k + 1 ∧ AllPrimesExceed (choose n k) k

/-- The function g(k): smallest n > k+1 with all prime factors of C(n,k) > k.
    Defined constructively via Nat.find from the existence axiom. -/
noncomputable def gFunc (k : ℕ) : ℕ :=
  Nat.find (gFunc_exists k)

/-- g(k) > k + 1 (from Nat.find_spec). -/
theorem gFunc_gt (k : ℕ) : gFunc k > k + 1 :=
  (Nat.find_spec (gFunc_exists k)).1

/-- All prime factors of C(g(k), k) exceed k (from Nat.find_spec). -/
theorem gFunc_spec (k : ℕ) : AllPrimesExceed (choose (gFunc k) k) k :=
  (Nat.find_spec (gFunc_exists k)).2

/-- g(k) is minimal: no smaller n > k+1 satisfies the condition (from Nat.find_min'). -/
theorem gFunc_minimal (k n : ℕ) (hn : n > k + 1) (h : AllPrimesExceed (choose n k) k) :
    gFunc k ≤ n :=
  Nat.find_min' (gFunc_exists k) ⟨hn, h⟩

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
# Part 5a: Concrete values of g(k)

We compute g(1) = 3 and g(2) = 6 from the axioms.
-/

/-- AllPrimesExceed is vacuously true for k < 2 (no primes ≤ 1). -/
private theorem allPrimesExceed_of_lt_two (m : ℕ) (k : ℕ) (hk : k < 2) :
    AllPrimesExceed m k :=
  fun p hp hpk _ => absurd (lt_of_le_of_lt hpk hk) (not_lt.mpr hp.two_le)

/-- g(1) = 3: for k=1, AllPrimesExceed is vacuously true (no primes ≤ 1),
    so g(1) is the smallest n > 2, which is 3. -/
theorem gFunc_one : gFunc 1 = 3 := by
  apply le_antisymm
  · -- g(1) ≤ 3: n=3 > 1+1 and AllPrimesExceed (C(3,1)) 1 holds vacuously
    exact gFunc_minimal 1 3 (by omega) (allPrimesExceed_of_lt_two _ 1 (by omega))
  · -- g(1) ≥ 3: from g(1) > 1+1 = 2
    have := gFunc_gt 1; omega

/-- 2 divides C(4,2) = 6, so AllPrimesExceed fails for n=4, k=2. -/
private theorem not_allPrimesExceed_choose_4_2 : ¬AllPrimesExceed (choose 4 2) 2 :=
  not_allPrimesExceed_of_prime_dvd Nat.prime_two le_rfl (by decide)

/-- 2 divides C(5,2) = 10, so AllPrimesExceed fails for n=5, k=2. -/
private theorem not_allPrimesExceed_choose_5_2 : ¬AllPrimesExceed (choose 5 2) 2 :=
  not_allPrimesExceed_of_prime_dvd Nat.prime_two le_rfl (by decide)

/-- AllPrimesExceed (C(6,2)) 2: C(6,2) = 15 = 3·5, and 2 ∤ 15. -/
private theorem allPrimesExceed_choose_6_2 : AllPrimesExceed (choose 6 2) 2 := by
  intro p hp hpk hpdvd
  -- p is prime and p ≤ 2, so p = 2
  have hp2 : p = 2 := le_antisymm hpk hp.two_le
  subst hp2
  -- 2 ∤ 15
  exact absurd hpdvd (by decide)

/-- g(2) = 6: the smallest n > 3 with C(n,2) having no prime factor ≤ 2.
    n=4: C(4,2)=6, 2|6 → fails. n=5: C(5,2)=10, 2|10 → fails.
    n=6: C(6,2)=15, 2∤15 → succeeds. -/
theorem gFunc_two : gFunc 2 = 6 := by
  apply le_antisymm
  · -- g(2) ≤ 6
    exact gFunc_minimal 2 6 (by omega) allPrimesExceed_choose_6_2
  · -- g(2) ≥ 6: g(2) > 3, and g(2) ≠ 4, g(2) ≠ 5
    have hgt := gFunc_gt 2  -- g(2) > 3
    -- Rule out g(2) = 4 and g(2) = 5
    suffices h : gFunc 2 ≠ 4 ∧ gFunc 2 ≠ 5 by omega
    exact ⟨fun h4 => not_allPrimesExceed_choose_4_2 (h4 ▸ gFunc_spec 2),
           fun h5 => not_allPrimesExceed_choose_5_2 (h5 ▸ gFunc_spec 2)⟩

/-
# Part 5b: Computing g(3) and g(4)

g(3) = g(4) = 7, since C(7,3) = C(7,4) = 35 = 5·7 has no prime factor ≤ 4.
-/

/-- C(5,3) = 10 is even. -/
private theorem not_allPrimesExceed_choose_5_3 : ¬AllPrimesExceed (choose 5 3) 3 :=
  not_allPrimesExceed_of_prime_dvd Nat.prime_two (by omega) (by decide)

/-- C(6,3) = 20 is even. -/
private theorem not_allPrimesExceed_choose_6_3 : ¬AllPrimesExceed (choose 6 3) 3 :=
  not_allPrimesExceed_of_prime_dvd Nat.prime_two (by omega) (by decide)

/-- AllPrimesExceed (C(7,3)) 3: C(7,3) = 35 = 5·7, no prime ≤ 3 divides. -/
private theorem allPrimesExceed_choose_7_3 : AllPrimesExceed (choose 7 3) 3 := by
  intro p hp hpk hpdvd
  have : p = 2 ∨ p = 3 := by have := hp.two_le; omega
  rcases this with rfl | rfl <;> exact absurd hpdvd (by decide)

/-- g(3) = 7: C(5,3)=10 (2|10), C(6,3)=20 (2|20), C(7,3)=35 (5·7, succeeds). -/
theorem gFunc_three : gFunc 3 = 7 := by
  apply le_antisymm
  · exact gFunc_minimal 3 7 (by omega) allPrimesExceed_choose_7_3
  · have hgt := gFunc_gt 3
    suffices h : gFunc 3 ≠ 5 ∧ gFunc 3 ≠ 6 by omega
    exact ⟨fun h5 => not_allPrimesExceed_choose_5_3 (h5 ▸ gFunc_spec 3),
           fun h6 => not_allPrimesExceed_choose_6_3 (h6 ▸ gFunc_spec 3)⟩

/-- C(6,4) = 15, and 3 | 15. -/
private theorem not_allPrimesExceed_choose_6_4 : ¬AllPrimesExceed (choose 6 4) 4 :=
  not_allPrimesExceed_of_prime_dvd (by decide : Nat.Prime 3) (by omega) (by decide)

/-- AllPrimesExceed (C(7,4)) 4: C(7,4) = 35, no prime ≤ 4 divides. -/
private theorem allPrimesExceed_choose_7_4 : AllPrimesExceed (choose 7 4) 4 := by
  intro p hp hpk hpdvd
  have : p = 2 ∨ p = 3 ∨ p = 4 := by have := hp.two_le; omega
  rcases this with rfl | rfl | rfl
  · exact absurd hpdvd (by decide)
  · exact absurd hpdvd (by decide)
  · exact absurd hp (by decide)

/-- g(4) = 7: C(6,4)=15 (3|15), C(7,4)=35 (5·7, no primes ≤ 4). -/
theorem gFunc_four : gFunc 4 = 7 := by
  apply le_antisymm
  · exact gFunc_minimal 4 7 (by omega) allPrimesExceed_choose_7_4
  · have hgt := gFunc_gt 4
    suffices h : gFunc 4 ≠ 6 by omega
    exact fun h6 => not_allPrimesExceed_choose_6_4 (h6 ▸ gFunc_spec 4)

/-
# Part 5c: Computing g(5) = 23

g(5) is the smallest n > 6 with all prime factors of C(n,5) exceeding 5.
C(n,5) has a factor ≤ 5 for n = 7..22 (all even or divisible by 3).
C(23,5) = 33649 = 7·11·19·23 has all primes > 5.
-/

/-- AllPrimesExceed (C(23,5)) 5: C(23,5) = 33649 = 7·11·19·23, no prime ≤ 5. -/
private theorem allPrimesExceed_choose_23_5 : AllPrimesExceed (choose 23 5) 5 := by
  intro p hp hpk hpdvd
  have := hp.two_le
  interval_cases p <;> exact absurd hpdvd (by decide)

/-- g(5) = 23: for n=7..22, C(n,5) always has a prime factor ≤ 5. -/
theorem gFunc_five : gFunc 5 = 23 := by
  apply le_antisymm
  · exact gFunc_minimal 5 23 (by omega) allPrimesExceed_choose_23_5
  · have hgt := gFunc_gt 5
    by_contra hlt
    push_neg at hlt
    suffices h : ∀ n, 7 ≤ n → n ≤ 22 → ¬AllPrimesExceed (choose n 5) 5 by
      exact h (gFunc 5) (by omega) (by omega) (gFunc_spec 5)
    intro n hn1 hn2
    interval_cases n <;>
    first
    | exact not_allPrimesExceed_of_prime_dvd Nat.prime_two (by omega) (by decide)
    | exact not_allPrimesExceed_of_prime_dvd (by decide : Nat.Prime 3) (by omega) (by decide)

/-
# Part 5d: Computing g(6) = 62

g(6) is the smallest n > 7 with all prime factors of C(n,6) exceeding 6.
C(62,6) = 61474519 = 19·29·31·59·61 has all primes > 6.
-/

/-- AllPrimesExceed (C(62,6)) 6: C(62,6) = 61474519 = 19·29·31·59·61, no prime ≤ 6. -/
private theorem allPrimesExceed_choose_62_6 : AllPrimesExceed (choose 62 6) 6 := by
  intro p hp hpk hpdvd
  have := hp.two_le
  interval_cases p <;> exact absurd hpdvd (by decide)

/-- g(6) = 62: for n=8..61, C(n,6) always has a prime factor ≤ 6. -/
theorem gFunc_six : gFunc 6 = 62 := by
  apply le_antisymm
  · exact gFunc_minimal 6 62 (by omega) allPrimesExceed_choose_62_6
  · have hgt := gFunc_gt 6
    by_contra hlt
    push_neg at hlt
    suffices h : ∀ n, 8 ≤ n → n ≤ 61 → ¬AllPrimesExceed (choose n 6) 6 by
      exact h (gFunc 6) (by omega) (by omega) (gFunc_spec 6)
    intro n hn1 hn2
    interval_cases n <;>
    first
    | exact not_allPrimesExceed_of_prime_dvd Nat.prime_two (by omega) (by decide)
    | exact not_allPrimesExceed_of_prime_dvd (by decide : Nat.Prime 3) (by omega) (by decide)
    | exact not_allPrimesExceed_of_prime_dvd (by decide : Nat.Prime 5) (by omega) (by decide)

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

This conjecture remains OPEN.
-/

/-- The asymptotic conjecture: log g(k) / (k / log k) → c for some c > 0.
    This means g(k) ~ exp(c · k / log k), between polynomial and exponential. -/
def ErdosAsymptoticConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Tendsto (fun k : ℕ => Real.log (gFunc k : ℝ) / ((k : ℝ) / Real.log (k : ℝ)))
      atTop (nhds c)

/-- Weaker statement: g(k) grows faster than any fixed polynomial. -/
def ErdosProblem1095OQ01 : Prop :=
  ∃ c : ℕ, c > 0 ∧ ∀ k : ℕ, k > 0 → gFunc k > k ^ c

/-- Concrete values (proved from axioms). -/
example : gFunc 1 = 3 := gFunc_one
example : gFunc 2 = 6 := gFunc_two
example : gFunc 3 = 7 := gFunc_three
example : gFunc 4 = 7 := gFunc_four
example : gFunc 5 = 23 := gFunc_five
example : gFunc 6 = 62 := gFunc_six

end Erdos1095OQ01
