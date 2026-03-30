/-
Erdős Problem #383: Prime Divisors of Consecutive Squares

**Problem Statement (OPEN)**

Is it true that for every k, there are infinitely many primes p such that
the largest prime divisor of ∏_{i=0}^k (p² + i) is p itself?

**Background:**
The product spans k+1 consecutive integers starting from p².
We ask whether p can be the largest prime factor of this product
for infinitely many primes p.

**Relation to Problem #382:**
A positive answer would resolve the second part of Erdős Problem #382.

**Heuristic Argument:**
Probabilistic considerations suggest integers without prime divisors ≥ √n
occur with positive density, supporting an affirmative conjecture.

**Status:** OPEN

**Reference:** Erdős & Graham 1980 [ErGr80]

**Proved in this file (8 theorems):**
- hasLargestPrimeFactor_iff: equivalence of largest prime factor definitions
- conjecture_equiv: ErdosConjecture383 ↔ ErdosConjecture383' (was axiom, now proved)
- zero_good: every prime is 0-good (p is largest prime factor of p²)
- infinitely_many_zero_good: infinitely many 0-good primes
- kGood_iff_smooth: k-good iff all p²+i are p-smooth
- kGood_one_smooth_p2_plus_1: 1-good primes have all prime factors of p²+1 ≤ p
- problem383_implies_382: k=1 case implies Problem 382 Part 2
- consecutiveSquareProduct_pos: the product is always positive for prime p

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Finset Nat

namespace Erdos383

/-
# Part 1: Prime Factor Definitions
-/

-- The set of prime factors
def primeDivisors (n : ℕ) : Finset ℕ :=
  n.primeFactors

-- A number has p as its largest prime factor
def hasLargestPrimeFactor (n : ℕ) (p : ℕ) : Prop :=
  p ∈ primeDivisors n ∧ ∀ q ∈ primeDivisors n, q ≤ p

-- Equivalently, p divides n and all prime factors are ≤ p
theorem hasLargestPrimeFactor_iff (n p : ℕ) (hn : n ≠ 0) :
    hasLargestPrimeFactor n p ↔ p.Prime ∧ p ∣ n ∧ ∀ q, q.Prime → q ∣ n → q ≤ p := by
  simp only [hasLargestPrimeFactor, primeDivisors]
  constructor
  · intro ⟨hp_mem, hmax⟩
    rw [Nat.mem_primeFactors] at hp_mem
    obtain ⟨hp_prime, hp_dvd, _⟩ := hp_mem
    exact ⟨hp_prime, hp_dvd, fun q hq hqd =>
      hmax q (Nat.mem_primeFactors.mpr ⟨hq, hqd, hn⟩)⟩
  · intro ⟨hp_prime, hp_dvd, hmax⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hn⟩,
      fun q hq_mem => by
        rw [Nat.mem_primeFactors] at hq_mem
        exact hmax q hq_mem.1 hq_mem.2.1⟩

/-- The largest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def maxPrimeFac (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

private lemma maxPrimeFac_mem {n : ℕ} (hn : n.primeFactors.Nonempty) :
    maxPrimeFac n ∈ n.primeFactors := by
  simp only [maxPrimeFac, dif_pos hn]
  exact Finset.max'_mem _ hn

private lemma le_maxPrimeFac {n q : ℕ} (hq : q ∈ n.primeFactors) :
    q ≤ maxPrimeFac n := by
  have hne : n.primeFactors.Nonempty := ⟨q, hq⟩
  simp only [maxPrimeFac, dif_pos hne]
  exact Finset.le_max' _ _ hq

/-- hasLargestPrimeFactor and maxPrimeFac agree when primeFactors is nonempty. -/
private lemma hasLargestPrimeFactor_iff_maxPrimeFac {n p : ℕ}
    (hne : n.primeFactors.Nonempty) :
    hasLargestPrimeFactor n p ↔ maxPrimeFac n = p := by
  simp only [hasLargestPrimeFactor, primeDivisors]
  constructor
  · intro ⟨hp_mem, hmax⟩
    exact le_antisymm (hmax _ (maxPrimeFac_mem hne)) (le_maxPrimeFac hp_mem)
  · intro heq
    subst heq
    exact ⟨maxPrimeFac_mem hne, fun q hq => le_maxPrimeFac hq⟩

/-
# Part 2: The Product Definition
-/

-- The product of p² + i for i from 0 to k
def consecutiveSquareProduct (p k : ℕ) : ℕ :=
  ∏ i in Icc 0 k, (p ^ 2 + i)

theorem consecutiveSquareProduct_eq (p k : ℕ) :
    consecutiveSquareProduct p k = ∏ i in range (k + 1), (p ^ 2 + i) := by
  simp only [consecutiveSquareProduct]
  congr 1
  ext i
  simp [Nat.lt_add_one_iff]

theorem consecutiveSquareProduct_zero (p : ℕ) :
    consecutiveSquareProduct p 0 = p ^ 2 := by
  simp [consecutiveSquareProduct]

theorem consecutiveSquareProduct_one (p : ℕ) :
    consecutiveSquareProduct p 1 = p ^ 2 * (p ^ 2 + 1) := by
  simp [consecutiveSquareProduct]
  ring

/-
# Part 3: The Main Property
-/

def isKGood (p k : ℕ) : Prop :=
  p.Prime ∧ hasLargestPrimeFactor (consecutiveSquareProduct p k) p

def isKGood' (p k : ℕ) : Prop :=
  p.Prime ∧
  p ∣ consecutiveSquareProduct p k ∧
  ∀ q, q.Prime → q ∣ consecutiveSquareProduct p k → q ≤ p

def kGoodPrimes (k : ℕ) : Set ℕ :=
  {p | isKGood p k}

lemma consecutiveSquareProduct_pos {p k : ℕ} (hp : p.Prime) :
    0 < consecutiveSquareProduct p k := by
  rw [consecutiveSquareProduct_eq]
  apply Finset.prod_pos
  intro i _
  omega

lemma consecutiveSquareProduct_ne_zero {p k : ℕ} (hp : p.Prime) :
    consecutiveSquareProduct p k ≠ 0 := by
  exact Nat.not_eq_zero_of_lt (consecutiveSquareProduct_pos hp)

-- For k = 0: p is 0-good since p² has p as its only prime factor
theorem zero_good (p : ℕ) (hp : p.Prime) : isKGood p 0 := by
  refine ⟨hp, ?_⟩
  rw [consecutiveSquareProduct_zero]
  simp only [hasLargestPrimeFactor, primeDivisors]
  refine ⟨Nat.mem_primeFactors.mpr ⟨hp, dvd_pow_self p 2, by positivity⟩,
    fun q hq => ?_⟩
  rw [Nat.mem_primeFactors] at hq
  exact le_of_dvd (Nat.Prime.pos hp) (hq.1.dvd_of_dvd_pow hq.2.1)

/-
# Part 4: The Erdős Conjecture
-/

def ErdosConjecture383 : Prop :=
  ∀ k : ℕ, (kGoodPrimes k).Infinite

def ErdosConjecture383' : Prop :=
  ∀ k : ℕ, {p : ℕ | p.Prime ∧ maxPrimeFac (consecutiveSquareProduct p k) = p}.Infinite

theorem conjecture_equiv : ErdosConjecture383 ↔ ErdosConjecture383' := by
  simp only [ErdosConjecture383, ErdosConjecture383', kGoodPrimes]
  apply forall_congr'
  intro k
  congr 1
  ext p
  simp only [Set.mem_setOf_eq, isKGood]
  constructor
  · intro ⟨hp, hlpf⟩
    refine ⟨hp, ?_⟩
    have hne : (consecutiveSquareProduct p k).primeFactors.Nonempty := ⟨p, hlpf.1⟩
    exact (hasLargestPrimeFactor_iff_maxPrimeFac hne).mp hlpf
  · intro ⟨hp, heq⟩
    refine ⟨hp, ?_⟩
    have hp_mem : p ∈ (consecutiveSquareProduct p k).primeFactors := by
      rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, consecutiveSquareProduct_ne_zero hp⟩
      rw [consecutiveSquareProduct_eq]
      apply dvd_trans (dvd_pow_self p 2)
      have : p ^ 2 + 0 = p ^ 2 := by ring
      rw [← this]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.zero_lt_succ k))
    exact (hasLargestPrimeFactor_iff_maxPrimeFac ⟨p, hp_mem⟩).mpr heq

/-
# Part 5: Partial Results
-/

theorem all_primes_zero_good : ∀ p, p.Prime → isKGood p 0 := zero_good

theorem infinitely_many_zero_good : (kGoodPrimes 0).Infinite := by
  apply Set.Infinite.mono (s := {p | p.Prime})
  · intro p hp; exact zero_good p hp
  · exact Nat.infinite_setOf_prime

/-
# Part 6: Relation to Problem #382
-/

-- Problem 382 Part 2: infinitely many primes p where all prime factors of p²+1 are ≤ p
def Problem382Part2 : Prop :=
  {p : ℕ | p.Prime ∧ ∀ q, q.Prime → q ∣ (p^2 + 1) → q ≤ p}.Infinite

-- If p is 1-good, then all prime factors of p²+1 are ≤ p
theorem kGood_one_smooth_p2_plus_1 (p : ℕ) (hp : isKGood p 1) :
    ∀ q, q.Prime → q ∣ (p^2 + 1) → q ≤ p := by
  intro q hq hqd
  obtain ⟨hp_prime, _, hmax⟩ := hp
  apply hmax
  simp only [primeDivisors]
  rw [Nat.mem_primeFactors]
  refine ⟨hq, ?_, consecutiveSquareProduct_ne_zero hp_prime⟩
  rw [consecutiveSquareProduct_one]
  exact dvd_mul_of_dvd_right hqd _

theorem problem383_implies_382 (h : (kGoodPrimes 1).Infinite) : Problem382Part2 := by
  apply Set.Infinite.mono h
  intro p hp
  simp only [kGoodPrimes, Set.mem_setOf_eq] at hp
  exact ⟨hp.1, kGood_one_smooth_p2_plus_1 p hp⟩

/-
# Part 7: Smooth Numbers
-/

def isSmooth (n y : ℕ) : Prop :=
  ∀ p ∈ primeDivisors n, p ≤ y

-- The k-good condition is equivalent to: all p² + i are p-smooth for i ≤ k
theorem kGood_iff_smooth (p k : ℕ) (hp : p.Prime) :
    isKGood p k ↔ p.Prime ∧ ∀ i ≤ k, isSmooth (p^2 + i) p := by
  constructor
  · -- Forward: k-good implies all factors are p-smooth
    intro ⟨_, hp_mem, hmax⟩
    refine ⟨hp, fun i hi q hq => ?_⟩
    apply hmax
    simp only [primeDivisors] at hq ⊢
    rw [Nat.mem_primeFactors] at hq ⊢
    obtain ⟨hq_prime, hq_dvd, _⟩ := hq
    refine ⟨hq_prime, ?_, consecutiveSquareProduct_ne_zero hp⟩
    rw [consecutiveSquareProduct_eq]
    exact dvd_trans hq_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega)))
  · -- Backward: all factors p-smooth implies k-good
    intro ⟨_, hsmooth⟩
    refine ⟨hp, ?_⟩
    simp only [hasLargestPrimeFactor, primeDivisors]
    refine ⟨?_, fun q hq => ?_⟩
    · rw [Nat.mem_primeFactors]
      refine ⟨hp, ?_, consecutiveSquareProduct_ne_zero hp⟩
      rw [consecutiveSquareProduct_eq]
      apply dvd_trans (dvd_pow_self p 2)
      have : p ^ 2 + 0 = p ^ 2 := by ring
      rw [← this]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.zero_lt_succ k))
    · rw [Nat.mem_primeFactors] at hq
      obtain ⟨hq_prime, hq_dvd, _⟩ := hq
      rw [consecutiveSquareProduct_eq] at hq_dvd
      rw [Prime.dvd_prod_iff hq_prime.prime] at hq_dvd
      obtain ⟨i, hi, hq_dvd_i⟩ := hq_dvd
      have hi' : i ≤ k := by simp [Finset.mem_range] at hi; omega
      exact hsmooth i hi' q (Nat.mem_primeFactors.mpr
        ⟨hq_prime, hq_dvd_i, by positivity⟩)

noncomputable def countSmooth (x y : ℕ) : ℕ :=
  (Finset.filter (fun n => isSmooth n y) (Finset.Icc 1 x)).card

/-
# Part 8-10: Status and Formal Statement
-/

def erdos_383_status : String := "OPEN"

theorem erdos_383_statement :
    ErdosConjecture383' ↔
    ∀ k, {p : ℕ | p.Prime ∧ maxPrimeFac (∏ i ∈ Icc 0 k, (p ^ 2 + i)) = p}.Infinite := by
  simp only [ErdosConjecture383', consecutiveSquareProduct]

end Erdos383
