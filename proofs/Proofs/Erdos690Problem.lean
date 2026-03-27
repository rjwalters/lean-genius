/-
Erdős Problem #690: Unimodality of k-th Prime Factor Density

Let d_k(p) be the density of integers whose k-th smallest prime factor
equals p. Is d_k(p) unimodal in p for fixed k ≥ 1?

Key Results:
- Erdős: p_k(n) ≈ e^{e^k} for almost all n; maximum of d_k at p ≈ e^{(1+o(1))k}
- Cambie (2025): d_k(p) IS unimodal for k ∈ {1, 2, 3}
- Cambie (2025): d_k(p) is NOT unimodal for 4 ≤ k ≤ 20
- Erdős believed the answer is no in general, but could not prove it

References:
- Erdős [Er79e]
- Cambie, arXiv:2501.10333 (2025)
- https://erdosproblems.com/690

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
## Core Definitions
-/

/-- The k-th smallest prime factor of n (0 if n has fewer than k prime factors). -/
noncomputable def kthSmallestPrimeFactor (n k : ℕ) : ℕ :=
  let factors := (Nat.factors n).toFinset.sort (· ≤ ·)
  if h : k < factors.length then factors.get ⟨k, h⟩ else 0

/-- The set of positive integers whose k-th smallest prime factor is p. -/
def kthPrimeFactorSet (k : ℕ) (p : ℕ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ kthSmallestPrimeFactor n k = p}

/-- The asymptotic density d_k(p): the density of integers whose k-th
    smallest prime factor equals p. Axiomatized as a real-valued function. -/
axiom kthPrimeFactorDensity (k : ℕ) (p : ℕ) : ℝ

/-- A function f : ℕ → ℝ is unimodal on primes: there exists a prime p*
    such that f is non-decreasing for primes ≤ p* and non-increasing
    for primes ≥ p*. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ p_star : ℕ, Nat.Prime p_star ∧
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p ≤ q → q ≤ p_star → f p ≤ f q) ∧
    (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p_star ≤ p → p ≤ q → f q ≤ f p)

/-
## Axiomatized Results
-/

/-- d_1(2) = 1/2: half of all positive integers have 2 as smallest prime factor. -/
axiom d1_at_2 : kthPrimeFactorDensity 1 2 = 1/2

/-- d_1(3) = (1/3)(1 - 1/2) = 1/6. -/
axiom d1_at_3 : kthPrimeFactorDensity 1 3 = 1/6

/-- d_1(5) = (1/5)(1 - 1/2)(1 - 1/3) = 1/15, the density of integers
    whose smallest prime factor is 5 (i.e., not divisible by 2 or 3). -/
axiom d1_at_5 : kthPrimeFactorDensity 1 5 = 1/15

/-- d_1 is strictly decreasing: the density of integers with smallest
    prime factor p decreases with p. Classical result via inclusion-exclusion:
    d_1(p) = (1/p) ∏_{q < p, q prime} (1 - 1/q). -/
axiom d1_strictly_decreasing :
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p < q →
    kthPrimeFactorDensity 1 q < kthPrimeFactorDensity 1 p

/-- **Cambie (2025)**: d_k(p) is unimodal for k = 2. -/
axiom cambie_unimodal_k2 :
  IsUnimodalOnPrimes (kthPrimeFactorDensity 2)

/-- **Cambie (2025)**: d_k(p) is unimodal for k = 3. -/
axiom cambie_unimodal_k3 :
  IsUnimodalOnPrimes (kthPrimeFactorDensity 3)

/-- **Cambie (2025)**: d_k(p) is NOT unimodal for 4 ≤ k ≤ 20. -/
axiom cambie_not_unimodal (k : ℕ) (hk : 4 ≤ k ∧ k ≤ 20) :
  ¬IsUnimodalOnPrimes (kthPrimeFactorDensity k)

/-
## Proved Theorems
-/

/-- d_1(p) is unimodal (trivially, since it is strictly decreasing).
    The peak is at p = 2, the smallest prime. For primes p ≤ q ≤ 2,
    both must equal 2. For 2 ≤ p ≤ q, strict decrease gives f(q) ≤ f(p).

    This eliminates the need for a separate axiom for k = 1 unimodality:
    it follows from the classical fact that d_1 is strictly decreasing. -/
theorem d1_unimodal :
    IsUnimodalOnPrimes (kthPrimeFactorDensity 1) := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · -- Non-decreasing for primes ≤ 2: only prime ≤ 2 is 2 itself
    intro p q hp _ hpq hq2
    -- hp.two_le gives 2 ≤ p, combined with p ≤ q ≤ 2 forces p = q
    have : p = q := by have := hp.two_le; omega
    subst this
  · -- Non-increasing for primes ≥ 2
    intro p q hp hq _ hpq
    rcases eq_or_lt_of_le hpq with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (d1_strictly_decreasing p q hp hq hlt)

/-- The answer to Erdős's question: unimodality fails for k ≥ 4.
    This follows immediately from Cambie's result for k = 4. -/
theorem erdos_690_answer_no :
    ¬∀ k : ℕ, k ≥ 1 → IsUnimodalOnPrimes (kthPrimeFactorDensity k) := by
  intro h
  have := h 4 (by omega)
  exact cambie_not_unimodal 4 ⟨le_refl 4, by omega⟩ this

/-- d_1(2) > d_1(3): even numbers are denser than those with smallest
    prime factor 3. Proved from the axiomatized values 1/2 and 1/6. -/
theorem d1_2_gt_d1_3 :
    kthPrimeFactorDensity 1 2 > kthPrimeFactorDensity 1 3 := by
  rw [d1_at_2, d1_at_3]; norm_num

/-- d_1(2) > d_1(3) also follows directly from d_1 being strictly decreasing. -/
theorem d1_2_gt_d1_3' :
    kthPrimeFactorDensity 1 2 > kthPrimeFactorDensity 1 3 :=
  d1_strictly_decreasing 2 3 (by norm_num) (by norm_num) (by omega)

/-- The peak of d_1 is at p = 2: for any prime q > 2, d_1(2) > d_1(q). -/
theorem d1_peak_at_2 (q : ℕ) (hq : Nat.Prime q) (h2 : 2 < q) :
    kthPrimeFactorDensity 1 q < kthPrimeFactorDensity 1 2 :=
  d1_strictly_decreasing 2 q (by norm_num) hq h2

/-- d_1(2) + d_1(3) = 2/3: the density of integers whose smallest
    prime factor is 2 or 3 accounts for exactly two-thirds. -/
theorem d1_sum_2_3 :
    kthPrimeFactorDensity 1 2 + kthPrimeFactorDensity 1 3 = 2/3 := by
  rw [d1_at_2, d1_at_3]; ring

/-- d_1(2) + d_1(3) + d_1(5) = 11/15: the first three primes account for
    73.3% of all positive integers. -/
theorem d1_sum_2_3_5 :
    kthPrimeFactorDensity 1 2 + kthPrimeFactorDensity 1 3 +
    kthPrimeFactorDensity 1 5 = 11/15 := by
  rw [d1_at_2, d1_at_3, d1_at_5]; ring

/-- Non-unimodality for k = 4 (the first counterexample). -/
theorem not_unimodal_k4 :
    ¬IsUnimodalOnPrimes (kthPrimeFactorDensity 4) :=
  cambie_not_unimodal 4 ⟨le_refl 4, by omega⟩

/-- Non-unimodality for k = 10. -/
theorem not_unimodal_k10 :
    ¬IsUnimodalOnPrimes (kthPrimeFactorDensity 10) :=
  cambie_not_unimodal 10 ⟨by omega, by omega⟩

/-- Non-unimodality for k = 20 (the largest k verified by Cambie). -/
theorem not_unimodal_k20 :
    ¬IsUnimodalOnPrimes (kthPrimeFactorDensity 20) :=
  cambie_not_unimodal 20 ⟨by omega, le_refl 20⟩

/-- Summary of complete picture:
    - k = 1: trivially unimodal (strictly decreasing) — PROVED
    - k = 2, 3: unimodal (Cambie 2025) — axiomatized
    - k = 4, ..., 20: NOT unimodal (Cambie 2025) — axiomatized
    - k > 20: open, but expected to not be unimodal -/
theorem erdos_690_summary :
    -- Small k: unimodal
    IsUnimodalOnPrimes (kthPrimeFactorDensity 1) ∧
    IsUnimodalOnPrimes (kthPrimeFactorDensity 2) ∧
    IsUnimodalOnPrimes (kthPrimeFactorDensity 3) ∧
    -- k = 4: not unimodal
    ¬IsUnimodalOnPrimes (kthPrimeFactorDensity 4) :=
  ⟨d1_unimodal, cambie_unimodal_k2, cambie_unimodal_k3,
   cambie_not_unimodal 4 ⟨le_refl 4, by omega⟩⟩
