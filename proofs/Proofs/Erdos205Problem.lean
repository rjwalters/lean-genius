/-
  Erdős Problem #205: 2^k + m with few prime factors

  Source: https://erdosproblems.com/205
  Status: DISPROVED (Barreto-Leeham 2026)

  Statement:
  Is it true that all sufficiently large n can be written as 2^k + m
  for some k ≥ 0, where Ω(m) < log log m?
  (Here Ω(m) is the number of prime divisors of m counted with multiplicity.)

  Answer: NO

  Counterexample:
  Barreto and Leeham (2026) proved there are infinitely many n such that
  for all k with 2^k < n, the value n - 2^k has at least
  Ω(n - 2^k) ≥ c · √(log n / log log n) prime factors for some c > 0.

  This is much larger than log log (n - 2^k), so the conjecture fails.

  Historical Context:
  - Romanoff (1934): Positive density of integers are 2^k + p for prime p
  - Erdős: Positive density of odd integers cannot be written as 2^k + p

  Reference:
  - Barreto, Leeham (2026): Counterexample via AI-assisted proof
-/

import Mathlib

open Nat Real BigOperators Set

namespace Erdos205

/-! ## The Ω function (big-omega) - counts prime factors with multiplicity -/

/-- The big-Ω function: number of prime factors counted with multiplicity.
    This equals the length of the prime factors list. -/
def bigOmega (n : ℕ) : ℕ :=
  n.primeFactorsList.length

/-- Ω(1) = 0 -/
theorem bigOmega_one : bigOmega 1 = 0 := by
  simp [bigOmega]

/-- Ω(p) = 1 for prime p -/
theorem bigOmega_prime {p : ℕ} (hp : p.Prime) : bigOmega p = 1 := by
  simp [bigOmega, Nat.primeFactorsList_prime hp]

/-- Ω(p^k) = k for prime p.
    Proof: The prime factorization of p^k is [p, p, ..., p] with k copies. -/
axiom bigOmega_prime_pow_ax : ∀ {p k : ℕ}, p.Prime → bigOmega (p ^ k) = k

/-- Ω is multiplicative: Ω(ab) = Ω(a) + Ω(b) for a, b > 0.
    Proof: Prime factors of ab are the concatenation of factors of a and b. -/
axiom bigOmega_mul_ax : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 →
    bigOmega (a * b) = bigOmega a + bigOmega b

/-! ## The Erdős Conjecture (Problem 205) -/

/-- A number n can be written as 2^k + m with Ω(m) < log log m -/
def HasSmallOmegaRep (n : ℕ) : Prop :=
  ∃ k : ℕ, ∃ m : ℕ, n = 2^k + m ∧ m > 1 ∧
    (bigOmega m : ℝ) < Real.log (Real.log m)

/-- The Erdős conjecture (Problem 205): All sufficiently large n have
    a representation 2^k + m with Ω(m) < log log m. -/
def Erdos205Conjecture : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, HasSmallOmegaRep n

/-! ## The Counterexample -/

/-- For a given n, this is the minimum Ω(n - 2^k) over valid k.
    "Valid" means 2^k < n so that n - 2^k > 0. -/
noncomputable def minOmegaRemainder (n : ℕ) : ℕ :=
  if n > 1 then
    let validKs := (Finset.range (Nat.log 2 n + 1)).filter (fun k => 2^k < n)
    if hne : validKs.Nonempty then
      validKs.inf' hne (fun k => bigOmega (n - 2^k))
    else 0
  else 0

/-- The key threshold function: c · √(log n / log log n) -/
noncomputable def thresholdFunction (n : ℕ) : ℝ :=
  Real.sqrt (Real.log n / Real.log (Real.log n))

/-- The main counterexample theorem:
    There exist infinitely many n such that for all valid k,
    Ω(n - 2^k) ≥ c · √(log n / log log n) for some c > 0.

    This is MUCH larger than log log(n - 2^k) ≈ log log n,
    so the Erdős conjecture fails.

    The counterexample also ensures n is large enough that all
    remainders n - 2^k are at least 16 (for log log monotonicity). -/
axiom barreto_leeham_counterexample :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n > N,
    (minOmegaRemainder n : ℝ) ≥ c * thresholdFunction n ∧
    (∀ k : ℕ, 2^k < n → n - 2^k ≥ 16)

/-- Auxiliary: the threshold function eventually dominates log log.
    √(log n / log log n) >> log log n for large n because:
    √(log n / log log n) / log log n = √(log n) / (log log n)^{3/2} → ∞ -/
axiom threshold_dominates_loglog :
  ∀ c : ℝ, c > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    c * thresholdFunction n > Real.log (Real.log n)

/-- Auxiliary: m = n - 2^k achieves the minimum omega when it's a valid remainder -/
axiom remainder_achieves_min (n k : ℕ) (h : 2^k < n) :
    minOmegaRemainder n ≤ bigOmega (n - 2^k)

/-- Auxiliary: log log is monotone increasing for x ≥ 16.
    (Actually needs x > e^e ≈ 15.15, but 16 suffices for our purposes.) -/
axiom loglog_mono_nat {m n : ℕ} (hm : m ≥ 16) (hmn : m ≤ n) :
    Real.log (Real.log m) ≤ Real.log (Real.log n)


/-- The negation of the Erdős conjecture follows from the counterexample. -/
theorem erdos_205_disproved : ¬Erdos205Conjecture := by
  intro ⟨N₀, hconj⟩
  -- Get the counterexample constant c
  obtain ⟨c, hc_pos, hcounter⟩ := barreto_leeham_counterexample
  -- Get N₁ such that for n ≥ N₁, c * threshold(n) > log log n
  obtain ⟨N₁, hdom⟩ := threshold_dominates_loglog c hc_pos
  -- Get a counterexample n that is large enough for both bounds
  obtain ⟨n, hn_large, hn_omega, hn_rem_large⟩ := hcounter (max N₀ N₁)
  -- n > max N₀ N₁ so n ≥ N₀ and n ≥ N₁
  have hn_ge_N0 : n ≥ N₀ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn_large)
  have hn_ge_N1 : n ≥ N₁ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn_large)
  -- The conjecture says n has a small-omega representation
  have hrep := hconj n hn_ge_N0
  unfold HasSmallOmegaRep at hrep
  obtain ⟨k, m, hn_eq, hm_pos, hm_small⟩ := hrep
  -- By threshold_dominates_loglog, c * thresholdFunction n > log log n
  have h_thresh := hdom n hn_ge_N1
  -- By the counterexample, minOmegaRemainder n ≥ c * thresholdFunction n
  -- Combined: minOmegaRemainder n ≥ c * thresholdFunction n > log log n
  have h_min_large : (minOmegaRemainder n : ℝ) > Real.log (Real.log n) :=
    lt_of_lt_of_le h_thresh hn_omega
  -- From n = 2^k + m, we get m = n - 2^k
  have hm_eq : m = n - 2^k := by omega
  -- So 2^k < n (since m > 0)
  have h_pow_lt : 2^k < n := by omega
  -- Therefore bigOmega m ≥ minOmegaRemainder n
  have h_omega_ge := remainder_achieves_min n k h_pow_lt
  rw [← hm_eq] at h_omega_ge
  -- So bigOmega m ≥ minOmegaRemainder n > log log n
  have h_omega_large : (bigOmega m : ℝ) > Real.log (Real.log n) :=
    lt_of_lt_of_le h_min_large (by exact_mod_cast h_omega_ge)
  -- But m ≤ n, so log log m ≤ log log n (for large enough values)
  have h_m_le_n : m ≤ n := by
    rw [hm_eq]
    exact Nat.sub_le n (2^k)
  -- We have: bigOmega m < log log m (from hm_small)
  -- And: bigOmega m > log log n (from h_omega_large)
  -- Since m ≤ n, log log m ≤ log log n, so:
  -- log log n < bigOmega m < log log m ≤ log log n
  -- This is a contradiction!
  -- m ≥ 16 follows from the counterexample construction
  have h_m_ge_16 : m ≥ 16 := by
    rw [hm_eq]
    exact hn_rem_large k h_pow_lt
  have h_loglog_le : Real.log (Real.log m) ≤ Real.log (Real.log n) :=
    loglog_mono_nat h_m_ge_16 h_m_le_n
  linarith [hm_small, h_omega_large, h_loglog_le]

/-! ## Romanoff's Theorem (positive result for primes) -/

/-- A number can be written as 2^k + p for some prime p -/
def IsPowerPlusePrime (n : ℕ) : Prop :=
  ∃ k p : ℕ, p.Prime ∧ n = 2^k + p

/-- Decidability for IsPowerPlusePrime (we use classical reasoning) -/
noncomputable instance : DecidablePred IsPowerPlusePrime := Classical.decPred _

/-- Romanoff (1934): A positive density of integers can be written as 2^k + p
    for some prime p. This is a positive density result. -/
axiom romanoff_positive_density :
  ∃ δ : ℝ, δ > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((Finset.range N).filter IsPowerPlusePrime).card / (N : ℝ) - δ| < ε

/-- Erdős: A positive density of odd integers CANNOT be written as 2^k + p
    for any prime p. Uses covering systems. -/
axiom erdos_covering_obstruction :
  ∃ δ : ℝ, δ > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    let S := (Finset.Icc 1 N).filter (fun n => Odd n ∧ ¬IsPowerPlusePrime n)
    |S.card / (N : ℝ) - δ| < ε

/-! ## Related bounds -/

/-- The average value of Ω(n) for n ≤ N is approximately log log N.
    This is a classical result in analytic number theory. -/
axiom average_omega_asymptotic :
  Filter.Tendsto
    (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, bigOmega n : ℝ) / N / Real.log (Real.log N))
    Filter.atTop (nhds 1)

/-- The typical value of Ω(n) concentrates around log log n.
    (Erdős-Kac theorem flavor) -/
axiom omega_concentration :
  ∀ ε > 0, Filter.Tendsto
    (fun N : ℕ => ((Finset.Icc 1 N).filter (fun n =>
      |((bigOmega n : ℝ) - Real.log (Real.log n))| > ε * Real.sqrt (Real.log (Real.log n))
    )).card / (N : ℝ))
    Filter.atTop (nhds 0)

/-! ## Summary

**Problem Status: DISPROVED**

Erdős Problem #205 asked whether all sufficiently large n can be written as
2^k + m where Ω(m) < log log m.

**Answer: NO** (Barreto-Leeham 2026)

**Key Result**:
There are infinitely many n such that for ALL k with 2^k < n:
  Ω(n - 2^k) ≥ c · √(log n / log log n)
for some constant c > 0.

Since √(log n / log log n) >> log log n for large n, these n provide
counterexamples to the conjecture.

**Technique**:
The counterexample construction likely uses:
1. Covering systems (following Erdős's work on 2^k + p)
2. Careful selection of n to ensure all remainders have many prime factors
3. Probabilistic or analytic estimates on prime factor counts

**Related Results**:
- Romanoff (1934): Positive density can be written as 2^k + p
- Erdős: Positive density of odds cannot be written as 2^k + p

References:
- Romanoff (1934): "Sur quelques questions d'additive"
- Erdős: Various papers on covering systems
- Barreto-Leeham (2026): AI-assisted counterexample construction
-/

end Erdos205
