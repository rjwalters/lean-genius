/-
Erdős Problem #695: Prime Chain Growth

**Problem Statement (OPEN)**

Let p₁ < p₂ < ⋯ be a sequence of primes where p_{i+1} ≡ 1 (mod p_i).
Such sequences are called "prime chains."

Two questions:
1. Is it true that lim_{k→∞} p_k^{1/k} = ∞?
2. Does there exist such a sequence with p_k ≤ exp(k(log k)^{1+o(1)})?

**Background:**
Prime chains arise from the multiplicative structure of cyclic groups.
If p_{i+1} ≡ 1 (mod p_i), then Z/p_{i+1}Z has a subgroup of order p_i.

**Status:** OPEN

**Reference:** [Er79e], [FKL10] (Ford-Konyagin-Luca)

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Filter Finset Real

namespace Erdos695

/-!
# Part 1: Prime Chain Definition

A prime chain is a strictly increasing sequence of primes where each
prime is congruent to 1 modulo the previous one.
-/

-- A prime chain: strictly increasing primes with p_{i+1} ≡ 1 (mod p_i)
def IsPrimeChain (p : ℕ → ℕ) : Prop :=
  StrictMono p ∧
  (∀ i, (p i).Prime) ∧
  (∀ i, p (i + 1) % p i = 1)

-- The divisibility condition: p_i | (p_{i+1} - 1)
def ChainDivisibility (p : ℕ → ℕ) : Prop :=
  ∀ i, p i ∣ (p (i + 1) - 1)

-- Equivalence of definitions
theorem chain_equiv (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) :
    (∀ i, p (i + 1) % p i = 1) ↔ ChainDivisibility p := by
  constructor
  · intro h i
    have := h i
    exact Nat.dvd_sub' (Nat.dvd_of_mod_eq_zero (by omega)) (Nat.dvd_refl _)
  · intro h i
    have := h i
    omega

/-!
# Part 2: Growth Questions

The key questions concern how fast prime chains must grow.
-/

-- The k-th root: p_k^{1/k}
noncomputable def kthRoot (p : ℕ → ℕ) (k : ℕ) : ℝ :=
  (p k : ℝ) ^ (1 / k : ℝ)

-- Question 1: Does p_k^{1/k} → ∞?
def Question1 : Prop :=
  ∀ p : ℕ → ℕ, IsPrimeChain p →
    Tendsto (kthRoot p) atTop atTop

-- This is equivalent to saying p_k grows faster than c^k for any c
theorem question1_equiv :
    Question1 ↔ ∀ p : ℕ → ℕ, IsPrimeChain p →
      ∀ c : ℝ, c > 0 → ∃ k₀ : ℕ, ∀ k ≥ k₀, (p k : ℝ) > c ^ k := by
  sorry

-- Question 2: Can p_k ≤ exp(k (log k)^{1+o(1)})?
def Question2 : Prop :=
  ∃ p : ℕ → ℕ, IsPrimeChain p ∧
    ∃ o : ℕ → ℝ, (o =o[atTop] (1 : ℕ → ℝ)) ∧
      ∀ k, (p k : ℝ) ≤ exp ((k + 1) * log (k + 1) ^ (1 + o k))

/-!
# Part 3: Known Bounds

We axiomatize what is known about prime chain growth.
-/

-- Linnik's theorem gives a bound on the least prime in an arithmetic progression
-- This implies greedy growth p_k ≤ exp(exp(O(k)))
axiom linnik_bound : ∃ L : ℕ, L > 0 ∧
  ∀ q : ℕ, q.Prime → ∃ p : ℕ, p.Prime ∧ p % q = 1 ∧ p ≤ q ^ L

-- Greedy algorithm produces a prime chain
axiom greedy_chain_exists : ∃ p : ℕ → ℕ, IsPrimeChain p

-- Greedy growth bound: p_k ≤ exp(exp(O(k)))
axiom greedy_doubly_exponential : ∃ C : ℝ, C > 0 ∧
  ∃ p : ℕ → ℕ, IsPrimeChain p ∧
    ∀ k, (p k : ℝ) ≤ exp (exp (C * k))

-- Conjectured: for any prime p, there exists p' ≤ p(log p)^{O(1)} with p' ≡ 1 (mod p)
axiom small_prime_conjecture : ∃ C : ℝ, C > 0 ∧
  ∀ p : ℕ, p.Prime → ∃ p' : ℕ, p'.Prime ∧ p' % p = 1 ∧
    (p' : ℝ) ≤ p * (log p) ^ C

-- If small_prime_conjecture holds, then Question2 is true
theorem conjecture_implies_question2 :
    (∃ C : ℝ, C > 0 ∧ ∀ p : ℕ, p.Prime → ∃ p' : ℕ, p'.Prime ∧ p' % p = 1 ∧
      (p' : ℝ) ≤ p * (log p) ^ C) → Question2 := by
  sorry

/-!
# Part 4: Related Sequences

Prime chains connect to OEIS A061092 and Cunningham chains.
-/

-- OEIS A061092: Smallest prime ≡ 1 (mod p_k) for k-th prime p_k
def smallestPrimeCongruentOne (p : ℕ) (hp : p.Prime) : ℕ :=
  Nat.find ⟨p + 1, sorry⟩  -- Existence by Dirichlet

-- Cunningham chain of the first kind: p, 2p+1, 4p+3, ...
def IsCunninghamChainFirst (p : ℕ → ℕ) : Prop :=
  (∀ i, (p i).Prime) ∧
  (∀ i, p (i + 1) = 2 * p i + 1)

-- Cunningham chains are prime chains (since 2p+1 ≡ 1 (mod p) when p is odd)
theorem cunningham_is_prime_chain (p : ℕ → ℕ) (h : IsCunninghamChainFirst p)
    (hodd : ∀ i, p i > 2) : StrictMono p ∧ (∀ i, p (i + 1) % p i = 1) := by
  sorry

/-!
# Part 5: The Ford-Konyagin-Luca Analysis

FKL (2010) conducted an extensive study of prime chain growth.
-/

-- FKL showed various bounds on prime chain lengths and growth
axiom fkl_analysis : ∃ f : ℕ → ℕ,
  (∀ n, ∃ p : ℕ → ℕ, IsPrimeChain p ∧ p 0 = 2 ∧
    (∀ k < f n, p k ≤ n)) ∧
  Tendsto f atTop atTop

-- Lower bound: every prime chain grows at least exponentially
axiom exponential_lower_bound : ∃ c : ℝ, c > 1 ∧
  ∀ p : ℕ → ℕ, IsPrimeChain p → ∀ k, (p k : ℝ) ≥ c ^ k

/-!
# Part 6: Problem Status

Both questions remain OPEN. The gap between known lower and upper bounds
on prime chain growth is substantial.
-/

-- The problem is open
def erdos_695_status : String := "OPEN"

-- Main theorem statements (both directions unknown)
def ErdosProblem695Part1 : Prop := Question1
def ErdosProblem695Part2 : Prop := Question2

-- Summary of what's known
-- Lower: p_k ≥ c^k for some c > 1 (exponential lower bound)
-- Upper: p_k ≤ exp(exp(O(k))) (greedy algorithm with Linnik)
-- Conjectured: p_k ≤ exp(k(log k)^{O(1)}) if small_prime_conjecture holds

/-!
# Part 7: Formal Statement from formal-conjectures

The following are the precise formal statements.
-/

-- Part 1: Does the k-th root tend to infinity?
theorem erdos_695_main :
    ∀ p : ℕ → ℕ, IsPrimeChain p →
      Tendsto (fun k => (p k : ℝ) ^ (1 / k : ℝ)) atTop atTop ↔
      Question1 := by
  intro p hp
  simp only [Question1]
  constructor <;> intro h
  · intro q hq
    exact h
  · exact h p hp

-- Part 2: Does there exist a chain with the bound?
theorem erdos_695_variant :
    Question2 ↔
    ∃ p : ℕ → ℕ, IsPrimeChain p ∧
      ∃ o : ℕ → ℝ, (o =o[atTop] (1 : ℕ → ℝ)) ∧
        ∀ k, (p k : ℝ) ≤ exp ((k + 1) * log (k + 1) ^ (1 + o k)) := by
  rfl

end Erdos695
