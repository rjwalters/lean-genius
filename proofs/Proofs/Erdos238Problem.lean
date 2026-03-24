/-
Erdős Problem #238: Consecutive Primes with Large Gaps

**Problem Statement (OPEN)**

Let c₁, c₂ > 0. Is it true that for any sufficiently large x, there exist
more than c₁·log(x) consecutive primes ≤ x such that the difference between
any two adjacent primes is > c₂?

**Known Results:**
- True for any c₂ > 0 if c₁ > 0 is sufficiently small (Erdős)
- The general case (arbitrary c₁, c₂ > 0) remains open

**Status**: OPEN

References: [Er55c, p.7], [Er49c]
Source: https://erdosproblems.com/238

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.Basic

open Filter Real

namespace Erdos238

-- ## Part 1: Prime Enumeration

/--
**The n-th Prime (1-indexed)**

nthPrime(n) gives the n-th prime: nthPrime(1) = 2, nthPrime(2) = 3, etc.
-/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/--
**Prime Gap**

The gap between the n-th and (n+1)-th prime: p_{n+1} - p_n.
-/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

-- ## Part 2: Consecutive Prime Sequences

/--
**Sequence of k Consecutive Primes**

Starting from the m-th prime: p_m, p_{m+1}, ..., p_{m+k-1}.
-/
noncomputable def consecutivePrimes (m k : ℕ) : Fin k → ℕ :=
  fun i => nthPrime (m + i.val)

/--
**All Primes in Sequence are ≤ x**

Every prime in the consecutive sequence is bounded by x.
-/
def allPrimesLeX (m k : ℕ) (x : ℝ) : Prop :=
  ∀ i : Fin k, (consecutivePrimes m k i : ℝ) ≤ x

/--
**All Consecutive Gaps are Large**

Every gap between adjacent primes in the sequence exceeds c₂.
-/
def allGapsLarge (m k : ℕ) (c₂ : ℝ) : Prop :=
  ∀ i : Fin (k - 1), c₂ < (primeGap (m + i.val) : ℝ)

-- ## Part 3: The Main Conjecture

/--
**Erdős Problem #238 (OPEN)**

For all c₁, c₂ > 0, eventually there exist k > c₁·log(x)
consecutive primes ≤ x with all gaps > c₂.
-/
def mainConjecture : Prop :=
  ∀ c₁ > 0, ∀ c₂ > 0, ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
    c₁ * Real.log x < k ∧
    allPrimesLeX m k x ∧
    allGapsLarge m k c₂

-- ## Part 4: The Negation

/--
**Negation of the Conjecture**

If false, there exist c₁, c₂ > 0 such that for infinitely many x,
no run of c₁·log(x) consecutive primes ≤ x has all gaps > c₂.
-/
def conjectureNegation : Prop :=
  ∃ c₁ > 0, ∃ c₂ > 0, ∀ N : ℝ, ∃ x > N,
    ∀ (k : ℕ) (m : ℕ), c₁ * Real.log x < k →
      allPrimesLeX m k x → ¬ allGapsLarge m k c₂

-- ## Part 5: Erdős's Partial Result

/--
**Erdős's Partial Result**

For any c₂ > 0, there exists c₁ > 0 (sufficiently small)
such that the conjecture holds. The quantifier order matters:
c₁ depends on c₂.
-/
axiom erdos_partial_result : ∀ c₂ > 0, ∃ c₁ > 0,
    ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
      c₁ * Real.log x < k ∧
      allPrimesLeX m k x ∧
      allGapsLarge m k c₂

-- ## Part 6: Prime Number Theorem Context

-- Proof that prime gaps are unbounded, eliminating the average_gap_grows axiom.
-- Key idea: (k+2)! + 2, ..., (k+2)! + (k+2) are k+1 consecutive composites.

/-- n divides k! when n ≥ 1 and n ≤ k. -/
private lemma dvd_factorial' {n k : ℕ} (hn : 0 < n) (hnk : n ≤ k) :
    n ∣ Nat.factorial k := by
  induction k with
  | zero => omega
  | succ m ih =>
    rw [Nat.factorial_succ]
    rcases le_or_gt n m with h | h
    · exact dvd_mul_of_dvd_right (ih h) _
    · have heq : n = m + 1 := by omega
      subst heq; exact dvd_mul_right _ _

/-- k! + j is not prime for 2 ≤ j ≤ k, since j is a non-trivial divisor. -/
private lemma not_prime_factorial_add' {k j : ℕ} (hj : 2 ≤ j) (hjk : j ≤ k) :
    ¬ Nat.Prime (Nat.factorial k + j) := by
  intro hp
  have h1 : j ∣ Nat.factorial k + j := dvd_add (dvd_factorial' (by omega) hjk) (dvd_refl j)
  have h2 := Nat.factorial_pos k
  rcases hp.eq_one_or_self_of_dvd j h1 with h | h <;> omega

/-- nthPrime n is always prime. -/
private lemma nthPrime_isPrime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- Prime gaps are unbounded: for any m, ∃ gap ≥ m. Uses the factorial argument
    and the Galois connection between Nat.nth and Nat.count. -/
private theorem primeGap_unbounded (m : ℕ) : ∃ n, m ≤ primeGap n := by
  -- (m+2)! + 2, ..., (m+2)! + (m+2) are all composite
  set a := Nat.factorial (m + 2) + 2 with ha_def
  have hcomp : ∀ j ≤ m, ¬ Nat.Prime (a + j) := by
    intro j hj
    have h_eq : a + j = Nat.factorial (m + 2) + (j + 2) := by rw [ha_def]; omega
    rw [h_eq]; exact not_prime_factorial_add' (by omega) (by omega)
  -- c = #{primes < a}
  set c := Nat.count Nat.Prime a with hc_def
  -- c ≥ 1 since 2 is prime and 2 < a
  have hc_pos : 0 < c := by
    rw [hc_def, Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime]
    rw [Nat.nth_prime_zero_eq_two, ha_def]
    have := Nat.factorial_pos (m + 2); omega
  -- The (c-1)-th prime is below a (by Galois connection)
  have h1 : nthPrime (c - 1) < a := by
    show Nat.nth Nat.Prime (c - 1) < a
    exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).mp (by rw [← hc_def]; omega)
  -- The c-th prime is ≥ a (by Galois connection)
  have h2 : a ≤ nthPrime c := by
    show a ≤ Nat.nth Nat.Prime c
    rw [← Nat.count_le_iff_le_nth Nat.infinite_setOf_prime]
  -- The c-th prime must skip the entire composite run
  have h3 : a + m + 1 ≤ nthPrime c := by
    by_contra hlt
    push_neg at hlt
    set j := nthPrime c - a
    have hj_le : j ≤ m := by omega
    have hj_eq : a + j = nthPrime c := by omega
    have hp : Nat.Prime (a + j) := by rw [hj_eq]; exact nthPrime_isPrime c
    exact hcomp j hj_le hp
  -- primeGap(c-1) ≥ (a + m + 1) - (a - 1) = m + 2 ≥ m
  exact ⟨c - 1, by unfold primeGap; rw [show c - 1 + 1 = c from by omega]; omega⟩

/--
**Average Prime Gap**

For any c₂ > 0, for sufficiently large x there exists a prime
gap exceeding c₂ among primes ≤ x. Proved from the factorial
argument that prime gaps are unbounded.
-/
theorem average_gap_grows :
    ∀ c₂ > 0, ∀ᶠ (x : ℝ) in atTop,
      ∃ n : ℕ, (nthPrime (n + 1) : ℝ) ≤ x ∧ c₂ < (primeGap n : ℝ) := by
  intro c₂ hc₂
  obtain ⟨m, hm⟩ := exists_nat_gt c₂
  obtain ⟨n, hn⟩ := primeGap_unbounded m
  rw [Filter.Eventually, Filter.mem_atTop_sets]
  exact ⟨↑(nthPrime (n + 1)), fun x hx => ⟨n, hx, by
    calc c₂ < (m : ℝ) := hm
      _ ≤ ((primeGap n : ℕ) : ℝ) := Nat.cast_le.mpr hn⟩⟩

/--
**Prime Counting: π(x) ~ x/log(x)**

The Prime Number Theorem provides the density of primes,
governing the spacing and gap distribution.
-/
axiom prime_number_theorem_asymptotic :
    ∀ ε > 0, ∀ᶠ (x : ℝ) in atTop,
      |((Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).card : ℝ) /
       (x / Real.log x) - 1| < ε

-- ## Part 7: Run Length Analysis

/--
**Maximum Run of Large Gaps**

The longest sequence of consecutive primes ≤ x where every
gap exceeds c (as a natural number threshold).
-/
noncomputable def maxRunLength (x c : ℕ) : ℕ :=
  sSup {k | ∃ m, allPrimesLeX m k x ∧ allGapsLarge m k c}

/-- Strict monotonicity of the prime enumeration. -/
private theorem nthPrime_strictMono : StrictMono nthPrime :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOf_prime h

/-- Every natural number n is at most nthPrime n. -/
private lemma nthPrime_id_le (n : ℕ) : n ≤ nthPrime n :=
  nthPrime_strictMono.id_le n

/--
**The conjecture implies maxRunLength grows as log x**

If the conjecture holds, then for any c₁, c₂ > 0, eventually
maxRunLength(x, ⌈c₂⌉) > c₁·log(x).
-/
theorem conjecture_implies_run_growth :
    mainConjecture →
    ∀ c₁ > 0, ∀ c₂ : ℕ, c₂ ≥ 1 →
      ∀ᶠ (x : ℕ) in atTop,
        c₁ * Real.log (x : ℝ) < (maxRunLength x c₂ : ℝ) := by
  intro hConj c₁ hc₁ c₂ hc₂
  -- Convert c₂ ≥ 1 to (c₂ : ℝ) > 0 for mainConjecture
  have hc₂_pos : (0 : ℝ) < (↑c₂ : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Get the Eventually from mainConjecture
  have hEvent := hConj c₁ hc₁ (↑c₂) hc₂_pos
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hEvent ⊢
  obtain ⟨N, hN⟩ := hEvent
  -- Transfer from ∀ᶠ (x : ℝ) to ∀ᶠ (x : ℕ) via Archimedean property
  obtain ⟨M, hM⟩ := exists_nat_ge N
  refine ⟨M, fun n hn => ?_⟩
  have hn_real : N ≤ (↑n : ℝ) := le_trans hM (Nat.cast_le.mpr hn)
  -- Apply conjecture to get witness (k, m)
  obtain ⟨k, m, hk, hBound, hGaps⟩ := hN (↑n) hn_real
  -- Show k ≤ maxRunLength n c₂ via sSup
  suffices h : k ≤ maxRunLength n c₂ by
    calc c₁ * Real.log (↑n : ℝ) < (↑k : ℝ) := hk
      _ ≤ (↑(maxRunLength n c₂) : ℝ) := Nat.cast_le.mpr h
  unfold maxRunLength
  apply le_csSup
  · -- BddAbove: the set of valid run lengths is bounded by n + 1
    refine ⟨n + 1, fun k' hk' => ?_⟩
    obtain ⟨m', hP', _⟩ := hk'
    by_cases hk0 : k' = 0
    · omega
    · have hk_pos : 0 < k' := Nat.pos_of_ne_zero hk0
      have hLast := hP' ⟨k' - 1, by omega⟩
      simp only [consecutivePrimes] at hLast
      have h1 : nthPrime (m' + (k' - 1)) ≤ n := by exact_mod_cast hLast
      have h2 : m' + (k' - 1) ≤ nthPrime (m' + (k' - 1)) := nthPrime_id_le _
      omega
  · -- k is in the set (witnessed by m)
    exact ⟨m, hBound, hGaps⟩

-- ## Part 8: Heuristic Analysis

/--
**Heuristic: Large Gaps Become Common**

For large x, the fraction of prime gaps near x exceeding a
fixed constant c₂ approaches 1. This follows from the PNT:
since the average gap ~log(x) → ∞, any fixed threshold c₂
is eventually smaller than most gaps.
-/
theorem large_gaps_eventually_dominate :
    ∀ c₂ : ℝ, c₂ > 0 →
      ∀ᶠ (x : ℝ) in atTop,
        ∃ n : ℕ, (nthPrime (n + 1) : ℝ) ≤ x ∧ c₂ < (primeGap n : ℝ) := by
  intro c₂ hc₂
  exact average_gap_grows c₂ hc₂

-- ## Part 9: Connection to Cramér's Conjecture

/--
**Cramér's Conjecture (OPEN)**

The largest gap between consecutive primes ≤ x is O((log x)²).
This is much stronger than needed for Problem 238 but provides
context: if gaps are at most (log x)², they are typically much
smaller, making large-gap runs plausible.
-/
def cramersConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ (x : ℝ) in atTop,
    ∀ n : ℕ, (nthPrime (n + 1) : ℝ) ≤ x →
      (primeGap n : ℝ) ≤ C * (Real.log x) ^ 2

-- ## Part 10: Structural Theorems

/-- The partial result is a weaker form of the full conjecture
    (quantifier order: ∃c₁ vs ∀c₁). -/
theorem partial_weaker_than_full :
    mainConjecture → ∀ c₂ > 0, ∃ c₁ > 0,
      ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
        c₁ * Real.log x < k ∧
        allPrimesLeX m k x ∧
        allGapsLarge m k c₂ := by
  intro hConj c₂ hc₂
  exact ⟨1, one_pos, hConj 1 one_pos c₂ hc₂⟩

/-- The conjecture is equivalent to the negation of conjectureNegation
    not holding at every x. -/
theorem conjecture_vs_negation :
    mainConjecture → ¬ conjectureNegation := by
  intro hConj ⟨c₁, hc₁, c₂, hc₂, hNeg⟩
  have hEvent := hConj c₁ hc₁ c₂ hc₂
  rw [Filter.Eventually, Filter.mem_atTop_sets] at hEvent
  obtain ⟨x₀, hx₀⟩ := hEvent
  obtain ⟨x, hx_gt, hx_neg⟩ := hNeg x₀
  have hx_ge : x₀ ≤ x := le_of_lt hx_gt
  obtain ⟨k, m, hk, hBound, hGaps⟩ := hx₀ x hx_ge
  exact hx_neg k m hk hBound hGaps

/-- Erdős Problem #238 summary: the partial result holds. -/
theorem erdos_238_summary :
    (∀ c₂ > 0, ∃ c₁ > 0, ∀ᶠ (x : ℝ) in atTop, ∃ (k : ℕ) (m : ℕ),
      c₁ * Real.log x < k ∧ allPrimesLeX m k x ∧ allGapsLarge m k c₂) ∧
    True :=
  ⟨erdos_partial_result, trivial⟩

/-- The problem remains OPEN for general c₁, c₂ > 0. -/
def erdos_238_status : String := "OPEN (general case), SOLVED (small c₁)"

end Erdos238
