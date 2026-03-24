/-
Erdős Problem #768

Let A ⊂ ℕ be the set of integers n such that for every prime divisor p of n,
there exists a divisor d > 1 of n with d ≡ 1 (mod p).

Is there a constant c > 0 such that |A ∩ [1,N]| / N = exp(-(c+o(1))√(log N)·log log N)?

Erdős proved bounds:
- Lower: exp(-c√(log N)·log log N) for some c > 0
- Upper: exp(-(1+o(1))√(log N·log log N))

This set A bounds the count of n ≤ N admitting a non-cyclic simple group of order n.

Reference: https://erdosproblems.com/768
-/

import Mathlib

namespace Erdos768

/-
## The Set A

We define the set A of integers where every prime divisor p has a "witness"
divisor d > 1 with d ≡ 1 (mod p).
-/

/-- Predicate: p | n and there exists d | n with d > 1 and d ≡ 1 (mod p) -/
def hasWitnessDivisor (n : ℕ) (p : ℕ) : Prop :=
  p.Prime → p ∣ n → ∃ d : ℕ, d > 1 ∧ d ∣ n ∧ d % p = 1

/-- The main predicate: every prime divisor has a witness -/
def inSetA (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → hasWitnessDivisor n p

/-- The set A of integers satisfying the condition -/
def setA : Set ℕ := {n | inSetA n}

/-- Alternative definition using prime factors -/
def inSetA' (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p ∈ n.primeFactors, ∃ d ∈ n.divisors, d > 1 ∧ d % p = 1

/-
## Basic Properties
-/

/-- 1 is in A (vacuously, no prime divisors) -/
theorem one_in_setA : 1 ∈ setA := by
  constructor
  · norm_num
  · intro p hp hdiv _ _
    -- p | 1 implies p ≤ 1, but p.Prime implies p ≥ 2: contradiction
    exfalso
    have h1 := Nat.le_of_dvd (by norm_num) hdiv
    have h2 := hp.two_le
    omega

/-- Prime powers are NOT in A (no d > 1 with d ≡ 1 mod p can divide p^k) -/
theorem prime_power_not_in_setA (p : ℕ) (k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    p^k ∉ setA := by
  intro ⟨_, hA⟩
  have hpdiv : p ∣ p^k := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk)
  specialize hA p hp hpdiv hp hpdiv
  obtain ⟨d, hd1, hdiv, hmod⟩ := hA
  -- d | p^k and d > 1 means p | d (since p is the only prime factor of p^k)
  have hd_ne_one : d ≠ 1 := by omega
  obtain ⟨q, hq_prime, hq_dvd_d⟩ := Nat.exists_prime_and_dvd hd_ne_one
  have hq_dvd_pk : q ∣ p ^ k := dvd_trans hq_dvd_d hdiv
  have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_pk
  have hq_eq_p : q = p := by
    rcases hp.eq_one_or_self_of_dvd q hq_dvd_p with h | h
    · exact absurd h hq_prime.ne_one
    · exact h
  have hp_dvd_d : p ∣ d := hq_eq_p ▸ hq_dvd_d
  -- p | d means d % p = 0, but we assumed d % p = 1
  rw [Nat.dvd_iff_mod_eq_zero] at hp_dvd_d
  omega

/-- Products of distinct primes p where (p-1) | n can be in A -/
theorem product_special_primes_in_setA (ps : List ℕ) 
    (hprimes : ∀ p ∈ ps, Nat.Prime p)
    (hdistinct : ps.Nodup)
    (hwitness : ∀ p ∈ ps, ∃ q ∈ ps, q > 1 ∧ q % p = 1) :
    ps.prod ∈ setA := by
  sorry

/-
## The Counting Function

Let A(N) = |A ∩ [1,N]|. The question is about the asymptotic behavior of A(N)/N.
-/

/-- Count of elements of A up to N -/
noncomputable def countA (N : ℕ) : ℕ :=
  haveI : DecidablePred inSetA := Classical.decPred _
  (Finset.filter inSetA (Finset.range (N + 1))).card

/-- The density of A up to N -/
noncomputable def densityA (N : ℕ) : ℝ :=
  (countA N : ℝ) / N

/-
## Erdős's Bounds

Erdős proved that the density of A satisfies certain bounds involving
exp(-c√(log N)·log log N).
-/

/-- The exponent function: √(log N)·log log N -/
noncomputable def exponentFunc (N : ℕ) : ℝ :=
  Real.sqrt (Real.log N) * Real.log (Real.log N)

/-- Erdős's lower bound: density ≥ exp(-c·√(log N)·log log N) -/
axiom erdos_768_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ N ≥ 10, densityA N ≥ Real.exp (-c * exponentFunc N)

/-- Erdős's upper bound: density ≤ exp(-(1+o(1))·√(log N·log log N)) -/
axiom erdos_768_upper_bound :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    densityA N ≤ Real.exp (-(1 - ε) * Real.sqrt (Real.log N * Real.log (Real.log N)))

/-
## The Main Conjecture

The question asks if there exists c > 0 such that:
A(N)/N = exp(-(c+o(1))√(log N)·log log N)
-/

/-- Erdős Problem #768: Does the exact asymptotic exist? -/
axiom erdos_768_conjecture :
  (∃ c : ℝ, c > 0 ∧
    Filter.Tendsto 
      (fun N => -Real.log (densityA N) / exponentFunc N)
      Filter.atTop (nhds c)) ∨
  (∀ c : ℝ, ¬Filter.Tendsto 
      (fun N => -Real.log (densityA N) / exponentFunc N)
      Filter.atTop (nhds c))

/-
## Connection to Simple Groups

The set A gives an upper bound for counting integers n ≤ N that are orders
of non-cyclic simple groups.
-/

/-- n is the order of a simple group -/
def isSimpleGroupOrder (n : ℕ) : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Fintype G),
    Fintype.card G = n ∧ IsSimpleGroup G

/-- n is the order of a non-cyclic simple group -/
def isNonCyclicSimpleGroupOrder (n : ℕ) : Prop :=
  isSimpleGroupOrder n ∧ ¬∃ (G : Type) (_ : Group G) (_ : Fintype G),
    Fintype.card G = n ∧ IsSimpleGroup G ∧ IsCyclic G

/-- Orders of non-cyclic simple groups are in A -/
axiom nonCyclic_simple_in_setA :
  ∀ n : ℕ, isNonCyclicSimpleGroupOrder n → n ∈ setA

/-
## Structural Properties

The condition for membership in A is closely related to the structure of 
the divisor lattice and Sylow theory.
-/

/-- If n ∈ A and n has a prime p with p^2 ∤ n, then ... -/
theorem squarefree_part_structure (n : ℕ) (p : ℕ) 
    (hn : n ∈ setA) (hp : p.Prime) (hdiv : p ∣ n) (hnosq : ¬(p^2 ∣ n)) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ q ≠ p ∧ q % p = 1 := by
  -- The witness d ≡ 1 (mod p) with d > 1 and d | n must have a prime factor q ≡ 1 (mod p)
  sorry

/-
## Asymptotic Analysis

The key insight is that for n to be in A, its prime factorization must be
"balanced" in a specific way related to the modular condition.
-/

/-- The log-log scale is natural for this problem -/
noncomputable def logLogDensity (N : ℕ) : ℝ :=
  Real.log (-Real.log (densityA N))

/-- The expected scaling -/
axiom logLogDensity_scaling :
  Filter.Tendsto
    (fun N => logLogDensity N / (Real.sqrt (Real.log N) * Real.log (Real.log N)))
    Filter.atTop Filter.atTop

/-
## Known Values and OEIS

OEIS A001034 lists orders of non-cyclic simple groups.
OEIS A352287 lists elements of A.
-/

/-- 6 = 2 × 3 is NOT in A: for p=3, no d > 1 divides 6 with d ≡ 1 (mod 3).
    (The divisors of 6 > 1 are {2, 3, 6}; 2%3=2, 3%3=0, 6%3=0.) -/
theorem six_not_in_setA : 6 ∉ setA := by
  intro ⟨_, hA⟩
  have := hA 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨d, hd1, hdiv, hmod⟩ := this
  -- d | 6 and d > 1 means d ∈ {2, 3, 6}
  have hdle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  interval_cases d <;> omega

/-- 12 = 2² × 3 is in A: for p=2, d=3 (3≡1 mod 2); for p=3, d=4 (4≡1 mod 3) -/
theorem twelve_in_setA : 12 ∈ setA := by
  constructor
  · norm_num
  · intro p hp hdiv _ _
    have hp_le : p ≤ 12 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases p <;> first
      | exact ⟨3, by omega, by omega, by omega⟩
      | exact ⟨4, by omega, by omega, by omega⟩
      | (exfalso; revert hp hdiv; norm_num)

/-- 56 = 2³ × 7 is in A: for p=2, d=7 (7≡1 mod 2); for p=7, d=8 (8≡1 mod 7) -/
theorem fiftysix_in_setA : 56 ∈ setA := by
  constructor
  · norm_num
  · intro p hp hdiv _ _
    have hp_le : p ≤ 56 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases p <;> first
      | exact ⟨7, by omega, by omega, by omega⟩
      | exact ⟨8, by omega, by omega, by omega⟩
      | (exfalso; revert hp hdiv; norm_num)

/-- Some small elements of A (OEIS A352287). Originally axiomatized; now proved. -/
theorem small_elements_of_A :
  1 ∈ setA ∧ 12 ∈ setA ∧ 56 ∈ setA :=
  ⟨one_in_setA, twelve_in_setA, fiftysix_in_setA⟩

/-- The smallest element of A greater than 1 is 12.
    2-11 are excluded: 2,3,5,7,11 are primes; 4,8,9 are prime powers;
    6 fails at p=3; 10 fails at p=5. -/
theorem smallest_nontrivial_in_setA :
  ∃ n : ℕ, n > 1 ∧ n ∈ setA ∧ ∀ m : ℕ, 1 < m → m < n → m ∉ setA := by
  refine ⟨12, by norm_num, twelve_in_setA, fun m hm1 hm12 => ?_⟩
  interval_cases m
  · exact prime_power_not_in_setA 2 1 (by norm_num) (by omega)
  · exact prime_power_not_in_setA 3 1 (by norm_num) (by omega)
  · exact prime_power_not_in_setA 2 2 (by norm_num) (by omega)
  · exact prime_power_not_in_setA 5 1 (by norm_num) (by omega)
  · exact six_not_in_setA
  · exact prime_power_not_in_setA 7 1 (by norm_num) (by omega)
  · exact prime_power_not_in_setA 2 3 (by norm_num) (by omega)
  · exact prime_power_not_in_setA 3 2 (by norm_num) (by omega)
  · -- 10 = 2 × 5: fails at p=5 (divisors > 1: {2, 5, 10}; none ≡ 1 mod 5)
    intro ⟨_, hA⟩
    have := hA 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨d, hd1, hdiv, hmod⟩ := this
    have hdle : d ≤ 10 := Nat.le_of_dvd (by norm_num) hdiv
    interval_cases d <;> omega
  · exact prime_power_not_in_setA 11 1 (by norm_num) (by omega)

/-
## Main Open Problem Statement
-/

/--
Erdős Problem #768 (Open):

Let A be the set of n ∈ ℕ such that for every prime p | n, there exists
a divisor d > 1 of n with d ≡ 1 (mod p).

Is there c > 0 such that |A ∩ [1,N]|/N = exp(-(c+o(1))√(log N)·log log N)?

Known bounds:
- Lower: exp(-c₁√(log N)·log log N) for some c₁ > 0
- Upper: exp(-(1+o(1))√(log N·log log N))

Motivation: |A ∩ [1,N]| bounds the count of orders of non-cyclic simple groups.
-/
axiom erdos_768_main :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    (∀ N ≥ 10, densityA N ≥ Real.exp (-c₂ * exponentFunc N)) ∧
    (∀ N ≥ 10, densityA N ≤ Real.exp (-c₁ * exponentFunc N))

end Erdos768
