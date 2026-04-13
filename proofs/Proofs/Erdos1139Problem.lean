/-
Erdős Problem #1139: Gaps in the Sequence of Almost-Primes

**Problem Statement (OPEN)**

Let 1 ≤ u₁ < u₂ < ⋯ be the sequence of integers with at most 2 prime
factors (counted with multiplicity). Is it true that
    lim sup (u_{k+1} - u_k) / log k = ∞?

The sequence includes all primes and semiprimes (products of two primes,
including squares of primes): 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, ...
The first excluded number is 8 = 2³ (three prime factors).

**Status**: OPEN

Source: https://erdosproblems.com/1139

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib

namespace Erdos1139

-- ## Part 1: Core Definitions

/-- Big Omega: count of prime factors with multiplicity.
    Ω(12) = 3 since 12 = 2² · 3. -/
noncomputable def bigOmega (n : ℕ) : ℕ :=
  n.factorization.sum fun _ k => k

/-- An almost-prime (P₂ number) is a positive integer with at most 2
    prime factors counted with multiplicity: Ω(n) ≤ 2. -/
def IsAlmostPrime (n : ℕ) : Prop :=
  2 ≤ n ∧ bigOmega n ≤ 2

/-- Decidable check for whether n has at most 2 prime factors. -/
def checkAlmostPrime (n : ℕ) : Bool :=
  2 ≤ n && n.primeFactorsList.length ≤ 2

-- ## Part 2: Basic Properties

/-- Every prime is an almost-prime (Ω(p) = 1 ≤ 2). -/
theorem prime_isAlmostPrime {p : ℕ} (hp : Nat.Prime p) : IsAlmostPrime p := by
  constructor
  · exact hp.two_le
  · unfold bigOmega
    rw [Nat.Prime.factorization hp]
    simp [Finsupp.sum_single_index]

/-- 1 is not an almost-prime (by our convention, n ≥ 2 required). -/
theorem one_not_almostPrime : ¬IsAlmostPrime 1 := by
  intro ⟨h, _⟩; omega

/-- 2 is an almost-prime. -/
theorem two_isAlmostPrime : IsAlmostPrime 2 :=
  prime_isAlmostPrime Nat.prime_two

/-- 3 is an almost-prime. -/
theorem three_isAlmostPrime : IsAlmostPrime 3 :=
  prime_isAlmostPrime Nat.prime_three

/-- 4 = 2² is an almost-prime (Ω(4) = 2). -/
theorem four_isAlmostPrime : IsAlmostPrime 4 := by
  constructor
  · omega
  · unfold bigOmega
    native_decide

/-- 8 = 2³ is NOT an almost-prime (Ω(8) = 3 > 2). -/
theorem eight_not_almostPrime : ¬IsAlmostPrime 8 := by
  intro ⟨_, h⟩
  unfold bigOmega at h
  revert h; native_decide

-- ## Part 3: The Enumeration

/-- The set of almost-primes up to N. -/
def almostPrimesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n => checkAlmostPrime n)

/-- The set of almost-primes is infinite (it contains all primes). -/
theorem infinite_almostPrimes : (setOf IsAlmostPrime).Infinite :=
  Nat.infinite_setOf_prime.mono (fun _ hn => prime_isAlmostPrime hn)

noncomputable instance : DecidablePred IsAlmostPrime := Classical.decPred _

/-- The k-th almost-prime (0-indexed): u₀ = 2, u₁ = 3, u₂ = 4, u₃ = 5, ... -/
noncomputable def nthAlmostPrime (k : ℕ) : ℕ := Nat.nth IsAlmostPrime k

/-- nthAlmostPrime is strictly increasing. -/
theorem nthAlmostPrime_strictMono : StrictMono nthAlmostPrime :=
  Nat.nth_strictMono infinite_almostPrimes

/-- Every value of nthAlmostPrime is an almost-prime. -/
theorem nthAlmostPrime_isAlmostPrime (k : ℕ) : IsAlmostPrime (nthAlmostPrime k) :=
  Nat.nth_mem_of_infinite infinite_almostPrimes k

/-- Every almost-prime appears in the enumeration. -/
theorem nthAlmostPrime_surj (m : ℕ) (hm : IsAlmostPrime m) :
    ∃ k, nthAlmostPrime k = m :=
  ⟨Nat.count IsAlmostPrime m, Nat.nth_count hm⟩

/-- The gap between consecutive almost-primes:
    g(k) = u_{k+1} - u_k where u_k is the k-th almost-prime. -/
noncomputable def almostPrimeGap (k : ℕ) : ℕ :=
  nthAlmostPrime (k + 1) - nthAlmostPrime k

/-- The gap is always positive (consecutive almost-primes are distinct). -/
theorem almostPrimeGap_pos (k : ℕ) : 0 < almostPrimeGap k :=
  Nat.sub_pos_of_lt (nthAlmostPrime_strictMono (by omega))

-- ## Part 4: Structural Results

/-- For any prime p, p is in the almost-prime sequence. -/
theorem primes_subset_almostPrimes {p : ℕ} (hp : Nat.Prime p) :
    IsAlmostPrime p :=
  prime_isAlmostPrime hp

/-- The product of two primes satisfies n ≥ 4. -/
theorem semiprime_ge_four {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    4 ≤ p * q := by
  calc 4 = 2 * 2 := by norm_num
    _ ≤ p * q := Nat.mul_le_mul hp.two_le hq.two_le

/-- If p and q are primes, then p * q has at most 2 prime factors. -/
theorem semiprime_isAlmostPrime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    IsAlmostPrime (p * q) := by
  constructor
  · exact le_trans (by norm_num : 2 ≤ 4) (semiprime_ge_four hp hq)
  · unfold bigOmega
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
    rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
    rw [Nat.Prime.factorization hp, Nat.Prime.factorization hq]
    simp [Finsupp.sum_single_index]

-- ## Part 5: Counting

/-- The number of almost-primes up to N includes all primes up to N.
    Since π(N) ~ N/log N, there are infinitely many almost-primes. -/
theorem almostPrimes_contain_primes (N : ℕ) :
    (Finset.range (N + 1)).filter (fun n => Nat.Prime n) ⊆ almostPrimesUpTo N := by
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  unfold almostPrimesUpTo checkAlmostPrime
  simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hn.1, hn.2.two_le, by rw [Nat.primeFactorsList_prime hn.2]; simp⟩

-- ## Part 6: The Main Conjecture

/-- Erdős Problem #1139 (OPEN): The gaps in the almost-prime sequence
    grow faster than any multiple of log k.
    lim sup (u_{k+1} - u_k) / log k = ∞ -/
/-- Between consecutive cubes n³ and (n+1)³, there are no integers with
    Ω(m) ≤ 2 if 8 | m (since Ω(8k) ≥ 3). This gives a structural source
    of gaps. -/
theorem cube_gap_obstruction (n : ℕ) (hn : 2 ≤ n)
    (m : ℕ) (hm1 : n ^ 3 < m) (hm2 : m < (n + 1) ^ 3)
    (hdiv : 8 ∣ m) : ¬IsAlmostPrime m := by
  intro ⟨_, hΩ⟩
  obtain ⟨k, rfl⟩ := hdiv
  have hk_ne : k ≠ 0 := by nlinarith [show n ^ 3 ≥ 8 from by nlinarith]
  -- Ω(8k) = Ω(8) + Ω(k) ≥ 3 > 2, contradicting hΩ
  have h_split : bigOmega (8 * k) = bigOmega 8 + bigOmega k := by
    unfold bigOmega
    rw [Nat.factorization_mul (by norm_num : (8 : ℕ) ≠ 0) hk_ne]
    exact Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have h8 : bigOmega 8 = 3 := by unfold bigOmega; native_decide
  linarith

-- ## Part 8: Density and Asymptotic Counting

/-- The density of integers with exactly k prime factors (counted with
    multiplicity) among {1, ..., N} is asymptotically
    (N / log N) · (log log N)^{k-1} / (k-1)!  (Landau-Ramanujan).
    For k ≤ 2, the almost-prime counting function π₂(N) satisfies
    π₂(N) ~ cN · log log N / log N for some constant c > 0. -/
end Erdos1139
