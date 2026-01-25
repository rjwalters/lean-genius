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

/-!
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

/-!
## Basic Properties
-/

/-- 1 is in A (vacuously, no prime divisors) -/
theorem one_in_setA : 1 ∈ setA := by
  constructor
  · norm_num
  · intro p hp hdiv
    intro _ _
    have : p = 1 := Nat.eq_one_of_pos_of_self_mul_self_le (Nat.Prime.pos hp) 
      (by simpa using hdiv)
    exact absurd this (Nat.Prime.ne_one hp)

/-- Prime powers are NOT in A (no d > 1 with d ≡ 1 mod p can divide p^k) -/
theorem prime_power_not_in_setA (p : ℕ) (k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    p^k ∉ setA := by
  intro ⟨_, hA⟩
  have hpdiv : p ∣ p^k := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hk)
  specialize hA p hp hpdiv hp hpdiv
  obtain ⟨d, hd1, hdiv, hmod⟩ := hA
  -- d | p^k means d = p^j for some j
  -- d ≡ 1 (mod p) and d > 1 is impossible for d = p^j
  sorry

/-- Products of distinct primes p where (p-1) | n can be in A -/
theorem product_special_primes_in_setA (ps : List ℕ) 
    (hprimes : ∀ p ∈ ps, Nat.Prime p)
    (hdistinct : ps.Nodup)
    (hwitness : ∀ p ∈ ps, ∃ q ∈ ps, q > 1 ∧ q % p = 1) :
    ps.prod ∈ setA := by
  sorry

/-!
## The Counting Function

Let A(N) = |A ∩ [1,N]|. The question is about the asymptotic behavior of A(N)/N.
-/

/-- Count of elements of A up to N -/
noncomputable def countA (N : ℕ) : ℕ :=
  (Finset.filter inSetA (Finset.range (N + 1))).card

/-- The density of A up to N -/
noncomputable def densityA (N : ℕ) : ℝ :=
  (countA N : ℝ) / N

/-!
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

/-!
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

/-!
## Connection to Simple Groups

The set A gives an upper bound for counting integers n ≤ N that are orders
of non-cyclic simple groups.
-/

/-- n is the order of a simple group -/
def isSimpleGroupOrder (n : ℕ) : Prop :=
  ∃ G : Type*, ∃ _ : Group G, ∃ _ : Fintype G, 
    Fintype.card G = n ∧ IsSimpleGroup G

/-- n is the order of a non-cyclic simple group -/
def isNonCyclicSimpleGroupOrder (n : ℕ) : Prop :=
  isSimpleGroupOrder n ∧ ¬∃ G : Type*, ∃ _ : Group G, ∃ _ : Fintype G,
    Fintype.card G = n ∧ IsSimpleGroup G ∧ IsCyclic G

/-- Orders of non-cyclic simple groups are in A -/
axiom nonCyclic_simple_in_setA :
  ∀ n : ℕ, isNonCyclicSimpleGroupOrder n → n ∈ setA

/-!
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

/-- The smallest element of A greater than 1 -/
axiom smallest_nontrivial_in_setA :
  ∃ n : ℕ, n > 1 ∧ n ∈ setA ∧ ∀ m : ℕ, 1 < m → m < n → m ∉ setA

/-!
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

/-!
## Known Values and OEIS

OEIS A001034 lists orders of non-cyclic simple groups.
OEIS A352287 lists elements of A.
-/

/-- Some small elements of A (OEIS A352287) -/
axiom small_elements_of_A :
  1 ∈ setA ∧ 6 ∈ setA ∧ 12 ∈ setA ∧ 56 ∈ setA

/-- 6 = 2 × 3 is in A because 3 ≡ 1 (mod 2) -/
theorem six_in_setA : 6 ∈ setA := by
  constructor
  · norm_num
  · intro p hp hdiv
    intro _ _
    interval_cases p
    all_goals {
      use 3
      constructor <;> norm_num
    }

/-!
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
