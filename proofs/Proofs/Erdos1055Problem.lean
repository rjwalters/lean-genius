/-!
# Erdős Problem #1055: Prime Classification by p+1 Factorization

Classify primes by the factorization structure of p+1:
- Class 1: all prime factors of p+1 are 2 or 3 (i.e., p+1 is 3-smooth)
- Class r: all prime factors of p+1 are in class ≤ r-1, with at least one
  prime factor in class exactly r-1.

## Key Questions
1. Are there infinitely many primes in each class?
2. How does p_r^{1/r} behave, where p_r is the least prime in class r?
   - Erdős conjectured p_r^{1/r} → ∞
   - Selfridge conjectured p_r^{1/r} is bounded

## Known Data
- Least primes by class: p_1=2, p_2=13, p_3=37, p_4=73, p_5=1021 (OEIS A005113)
- The count of primes ≤ n in class r is at most n^{o(1)}

## Status: OPEN

Reference: https://erdosproblems.com/1055
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The class of a prime p, defined recursively on the factorization of p+1.
    Class 1: all prime factors of p+1 are in {2, 3}.
    Class r (r ≥ 2): all prime factors of p+1 have class ≤ r-1,
    and at least one has class exactly r-1. -/
axiom primeClass (p : ℕ) : ℕ

/-- A prime p is in class r if primeClass p = r. -/
def IsInClass (p : ℕ) (r : ℕ) : Prop :=
  p.Prime ∧ primeClass p = r

/-- Class 1 primes: p+1 is 3-smooth (all prime factors are 2 or 3).
    Examples: 2 (2+1=3), 3 (3+1=4=2²), 5 (5+1=6=2·3),
    7 (7+1=8=2³), 11 (11+1=12=2²·3), 23 (23+1=24=2³·3). -/
axiom class_one_char (p : ℕ) (hp : p.Prime) :
    primeClass p = 1 ↔ ∀ q ∈ (p + 1).factors, q = 2 ∨ q = 3

/-! ## The Least Prime in Each Class -/

/-- p_r: the least prime in class r. -/
axiom leastPrimeInClass (r : ℕ) : ℕ

/-- p_r is prime and in class r (assuming the class is nonempty). -/
axiom leastPrime_spec (r : ℕ) (hr : r ≥ 1) :
    (leastPrimeInClass r).Prime ∧ primeClass (leastPrimeInClass r) = r

/-- p_r is minimal: no smaller prime is in class r. -/
axiom leastPrime_minimal (r : ℕ) (hr : r ≥ 1) (q : ℕ)
    (hq : q.Prime) (hc : primeClass q = r) :
    leastPrimeInClass r ≤ q

/-! ## Known Values (OEIS A005113) -/

/-- p_1 = 2: the smallest prime with 3-smooth successor (2+1=3). -/
axiom p_1 : leastPrimeInClass 1 = 2

/-- p_2 = 13: 13+1 = 14 = 2·7, and 7 is class 1 (7+1=8=2³). -/
axiom p_2 : leastPrimeInClass 2 = 13

/-- p_3 = 37: 37+1 = 38 = 2·19, and 19 is class 2. -/
axiom p_3 : leastPrimeInClass 3 = 37

/-- p_4 = 73: 73+1 = 74 = 2·37, and 37 is class 3. -/
axiom p_4 : leastPrimeInClass 4 = 73

/-- p_5 = 1021: 1021+1 = 1022 = 2·7·73, and 73 is class 4. -/
axiom p_5 : leastPrimeInClass 5 = 1021

/-! ## Existence: Each Class is Nonempty -/

/-- For every r ≥ 1, there exists a prime in class r. -/
axiom each_class_nonempty (r : ℕ) (hr : r ≥ 1) :
    ∃ p : ℕ, p.Prime ∧ primeClass p = r

/-! ## Conjecture 1: Infinitely Many Primes in Each Class -/

/-- Erdős Problem #1055 (main): For each r ≥ 1, there are infinitely many
    primes in class r. -/
axiom infinitely_many_in_each_class (r : ℕ) (hr : r ≥ 1) :
    Set.Infinite {p : ℕ | p.Prime ∧ primeClass p = r}

/-! ## Conjecture 2: Growth of p_r^{1/r} -/

/-- The sequence p_r^{1/r} for known values:
    p_1^1 = 2, p_2^{1/2} ≈ 3.61, p_3^{1/3} ≈ 3.33,
    p_4^{1/4} ≈ 2.92, p_5^{1/5} ≈ 4.01. -/

/-- Erdős's conjecture: p_r^{1/r} → ∞ as r → ∞.
    The least prime in class r grows superexponentially. -/
axiom erdos_growth_conjecture :
    Filter.Tendsto (fun r => ((leastPrimeInClass r : ℝ)) ^ ((1 : ℝ) / (r : ℝ)))
      Filter.atTop Filter.atTop

/-- Selfridge's competing conjecture: p_r^{1/r} is bounded.
    The least prime in class r grows at most exponentially.
    Note: exactly one of the Erdős and Selfridge conjectures can be true. -/
axiom selfridge_bounded_conjecture :
    ∃ M : ℝ, ∀ r : ℕ, r ≥ 1 →
      ((leastPrimeInClass r : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≤ M

/-! ## Density Bound -/

/-- The number of primes ≤ n in class r is at most n^{o(1)}.
    Each class contains a very sparse set of primes. -/
axiom class_density_bound (r : ℕ) (hr : r ≥ 1) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (Finset.card (Finset.filter (fun p => p.Prime ∧ primeClass p = r)
        (Finset.range (n + 1))) : ℝ) ≤ (n : ℝ) ^ ε

/-! ## Contradiction Between Conjectures -/

/-- The Erdős and Selfridge conjectures are contradictory:
    if p_r^{1/r} → ∞, it cannot be bounded. -/
axiom conjectures_contradict :
    ¬ (Filter.Tendsto (fun r => ((leastPrimeInClass r : ℝ)) ^ ((1 : ℝ) / (r : ℝ)))
         Filter.atTop Filter.atTop ∧
       ∃ M : ℝ, ∀ r : ℕ, r ≥ 1 →
         ((leastPrimeInClass r : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≤ M)
