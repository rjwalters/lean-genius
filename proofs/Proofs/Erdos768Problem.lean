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

/-- If p is prime and p divides a product of primes, then p is in the list. -/
private lemma prime_mem_of_dvd_list_prod {p : ℕ} (hp : p.Prime) {l : List ℕ}
    (hl : ∀ q ∈ l, q.Prime) (hdvd : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil => simp at hdvd; exact absurd hdvd hp.ne_one
  | cons a t ih =>
    simp only [List.prod_cons] at hdvd
    rcases hp.prime.dvd_or_dvd hdvd with ha | ht
    · -- p | a and both prime, so p = a
      have heq : p = a := by
        rcases (hl a (List.mem_cons_self a t)).eq_one_or_self_of_dvd p ha with h | h
        · exact absurd h hp.ne_one
        · exact h
      exact List.mem_cons.mpr (Or.inl heq)
    · exact List.mem_cons.mpr (Or.inr
        (ih (fun q hq => hl q (List.mem_cons_of_mem a hq)) ht))

/-- Products of distinct primes p where each has a witness q ≡ 1 (mod p) in the list
    are in A. The witness q divides the product since it's a list member. -/
theorem product_special_primes_in_setA (ps : List ℕ)
    (hprimes : ∀ p ∈ ps, Nat.Prime p)
    (hdistinct : ps.Nodup)
    (hwitness : ∀ p ∈ ps, ∃ q ∈ ps, q > 1 ∧ q % p = 1) :
    ps.prod ∈ setA := by
  constructor
  · -- Product of primes is positive
    exact List.prod_pos (fun p hp => (hprimes p hp).pos)
  · -- For each prime divisor of the product, find a witness
    intro p hp hdiv _ _
    -- p is prime and p | ps.prod, so p ∈ ps
    have hp_mem : p ∈ ps := prime_mem_of_dvd_list_prod hp hprimes hdiv
    -- The hypothesis provides a witness q ∈ ps
    obtain ⟨q, hq_mem, hq_gt, hq_mod⟩ := hwitness p hp_mem
    -- q divides ps.prod since q ∈ ps
    exact ⟨q, hq_gt, List.dvd_prod hq_mem, hq_mod⟩

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
/-- Erdős's upper bound: density ≤ exp(-(1+o(1))·√(log N·log log N)) -/
/-
## The Main Conjecture

The question asks if there exists c > 0 such that:
A(N)/N = exp(-(c+o(1))√(log N)·log log N)
-/

/-- Erdős Problem #768: Does the exact asymptotic exist? -/
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
/-
## Structural Properties

The condition for membership in A is closely related to the structure of 
the divisor lattice and Sylow theory.
-/

/-- NOTE: A previous version claimed that if n ∈ A and p | n with p² ∤ n, then
    some prime q | n has q ≡ 1 (mod p). This is FALSE:
    n = 12 ∈ A, p = 3, 3 | 12, 9 ∤ 12, but the only other prime divisor is 2,
    and 2 % 3 = 2 ≠ 1. The witness for p = 3 in n = 12 is d = 4 (composite,
    4 ≡ 1 mod 3), whose prime factor 2 does NOT satisfy 2 ≡ 1 (mod 3). -/

/-
## Asymptotic Analysis

The key insight is that for n to be in A, its prime factorization must be
"balanced" in a specific way related to the modular condition.
-/

/-- The log-log scale is natural for this problem -/
noncomputable def logLogDensity (N : ℕ) : ℝ :=
  Real.log (-Real.log (densityA N))

/-- The expected scaling -/
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
end Erdos768
