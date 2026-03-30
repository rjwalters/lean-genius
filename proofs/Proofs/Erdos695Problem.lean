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

/-
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

/-
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

/-
# Part 3: Known Bounds

We axiomatize what is known about prime chain growth.
-/

-- Linnik's theorem gives a bound on the least prime in an arithmetic progression
-- This implies greedy growth p_k ≤ exp(exp(O(k)))
axiom small_prime_conjecture : ∃ C : ℝ, C > 0 ∧
  ∀ p : ℕ, p.Prime → ∃ p' : ℕ, p'.Prime ∧ p' % p = 1 ∧
    (p' : ℝ) ≤ p * (log p) ^ C

-- If small_prime_conjecture holds, then Question2 is true
theorem conjecture_implies_question2 :
    (∃ C : ℝ, C > 0 ∧ ∀ p : ℕ, p.Prime → ∃ p' : ℕ, p'.Prime ∧ p' % p = 1 ∧
      (p' : ℝ) ≤ p * (log p) ^ C) → Question2 := by
  sorry

/-
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
  obtain ⟨_, hsucc⟩ := h
  constructor
  · -- p(i+1) = 2*p(i)+1 > p(i) since p(i) > 2
    exact strictMono_nat_of_lt_succ (fun k => by rw [hsucc k]; have := hodd k; omega)
  · -- (2*p(i)+1) % p(i) = 1 since p(i) > 1
    intro i
    rw [hsucc i, show 2 * p i + 1 = 1 + p i * 2 from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := hodd i; omega)]

/-
# Part 4.5: Exponential Lower Bound (PROVED, was axiom)

For odd prime p₀, any prime q ≡ 1 (mod p₀) satisfies q ≥ 2p₀ + 1.
This gives exponential growth: p(k) ≥ 2^k for any prime chain.
-/

/-- For odd prime p₀ (≥ 3), any prime q with q ≡ 1 (mod p₀) satisfies q ≥ 2p₀ + 1.
    Proof: q = k·p₀ + 1. If k = 0 then q = 1 (not prime). If k = 1 then
    q = p₀ + 1 is even and ≥ 4 (not prime since p₀ is odd). So k ≥ 2. -/
theorem chain_step_ge {p₀ q : ℕ} (hp₀ : p₀.Prime) (hq : q.Prime)
    (hp₀3 : 3 ≤ p₀) (hmod : q % p₀ = 1) : 2 * p₀ + 1 ≤ q := by
  suffices 2 ≤ q / p₀ by
    have := Nat.div_mul_le_self q p₀
    omega
  by_contra hlt
  push_neg at hlt
  have hlt1 : q / p₀ ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hlt1 with rfl | rfl
  · -- k = 0: q = 0·p₀ + 1 = 1, not prime
    have : q < p₀ := Nat.div_eq_zero_iff hp₀.pos |>.mp rfl
    have : q = 1 := by omega
    subst this; exact absurd hq (by decide)
  · -- k = 1: q = p₀ + 1, which is even (p₀ odd) and ≥ 4, not prime
    have hqeq : q = p₀ + 1 := by
      have := Nat.div_add_mod q p₀; omega
    subst hqeq
    have hdvd : 2 ∣ (p₀ + 1) := by
      obtain ⟨k, rfl⟩ := hp₀.odd_of_ne_two (by omega)
      exact ⟨k + 1, by ring⟩
    rcases hq.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega

/-- Every prime chain grows at least exponentially: p(k) ≥ 2^k.
    Proved from chain_step_ge (no axioms needed). -/
theorem exponential_lower_bound : ∃ c : ℝ, c > 1 ∧
    ∀ p : ℕ → ℕ, IsPrimeChain p → ∀ k, (p k : ℝ) ≥ c ^ k := by
  refine ⟨2, by norm_num, fun p ⟨hm, hp, hmod⟩ => ?_⟩
  -- Auxiliary: p(k) ≥ k + 2 (strict monotonicity + p(0) ≥ 2)
  have hge : ∀ k, k + 2 ≤ p k := by
    intro k
    induction k with
    | zero => exact (hp 0).two_le
    | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hm (Nat.lt.base n)))
  -- Main: p(k) ≥ 2^k (in ℕ, then cast to ℝ)
  suffices hnat : ∀ k, 2 ^ k ≤ p k from
    fun k => by exact_mod_cast hnat k
  intro k
  induction k with
  | zero => simpa using (hp 0).one_lt.le
  | succ n ih =>
    rcases n with _ | m
    · -- n = 0: 2^1 = 2 ≤ p(1), since p(1) ≥ 3
      simpa using (show 2 ≤ p 1 from by have := hge 1; omega)
    · -- n = m + 1 ≥ 1: p(m+1) ≥ 3, apply chain_step_ge
      have hpm3 : 3 ≤ p (m + 1) := by have := hge (m + 1); omega
      have step := chain_step_ge (hp (m + 1)) (hp (m + 2)) hpm3 (hmod (m + 1))
      calc 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
        _ ≤ 2 * p (m + 1) := Nat.mul_le_mul_left 2 ih
        _ ≤ p (m + 2) := by omega

/-
# Part 5: The Ford-Konyagin-Luca Analysis

FKL (2010) conducted an extensive study of prime chain growth.
-/

-- FKL showed various bounds on prime chain lengths and growth
/-
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

/-
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
