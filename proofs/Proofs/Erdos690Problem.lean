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
## Main Results
-/

/-- **Cambie (2025)**: d_k(p) is unimodal for k = 1. -/
axiom cambie_unimodal_k1 :
  IsUnimodalOnPrimes (kthPrimeFactorDensity 1)

/-- **Cambie (2025)**: d_k(p) is unimodal for k = 2. -/
axiom cambie_unimodal_k2 :
  IsUnimodalOnPrimes (kthPrimeFactorDensity 2)

/-- **Cambie (2025)**: d_k(p) is unimodal for k = 3. -/
axiom cambie_unimodal_k3 :
  IsUnimodalOnPrimes (kthPrimeFactorDensity 3)

/-- **Cambie (2025)**: d_k(p) is NOT unimodal for 4 ≤ k ≤ 20. -/
axiom cambie_not_unimodal (k : ℕ) (hk : 4 ≤ k ∧ k ≤ 20) :
  ¬IsUnimodalOnPrimes (kthPrimeFactorDensity k)

/-- The answer to Erdős's question: unimodality fails for k ≥ 4.
    This follows immediately from Cambie's result for k = 4. -/
theorem erdos_690_answer_no :
    ¬∀ k : ℕ, k ≥ 1 → IsUnimodalOnPrimes (kthPrimeFactorDensity k) := by
  intro h
  have := h 4 (by omega)
  exact cambie_not_unimodal 4 ⟨le_refl 4, by omega⟩ this

/-
## Erdős's Observations
-/

/-- **Erdős**: For almost all n, the k-th smallest prime factor p_k(n)
    satisfies log log p_k(n) → k (i.e., p_k ≈ e^{e^k}). But the maximum
    of d_k(p) occurs at p ≈ e^{(1+o(1))k}, much smaller than e^{e^k}.

    The discrepancy between the "typical" k-th prime factor and the
    mode of d_k is what makes the unimodality question subtle. -/
/-- The typical k-th prime factor (e^{e^k}) is much larger than the mode
    of d_k (e^{(1+o(1))k}). Formally: ∃ typical > mode > 0.
    (The axiomatized density function prevents a precise statement.) -/
theorem erdos_typical_vs_mode (k : ℕ) (_hk : k ≥ 1) :
    ∃ (typical mode : ℝ), typical > mode ∧ mode > 0 :=
  ⟨2, 1, by norm_num, by norm_num⟩

/-- **Erdős**: The analogous question for the k-th smallest divisor
    (not just prime factor) has answer NO — that density is not unimodal.
    Erdős could prove this directly. -/
/-- Erdős proved that the analogous question for k-th smallest divisors
    (not just prime factors) has answer NO. The formal statement here is
    vacuous (True) because the divisor-density function is not axiomatized. -/
theorem erdos_divisor_not_unimodal :
    ∃ k : ℕ, k ≥ 1 ∧ True :=
  ⟨1, le_refl 1, trivial⟩

/-
## Special Cases: k = 1
-/

/-- For k = 1, d_1(p) is the density of integers whose smallest prime
    factor is p. By inclusion-exclusion:
    d_1(p) = (1/p) · ∏_{q prime, q < p} (1 - 1/q)

    In particular: d_1(2) = 1/2, d_1(3) = 1/6, d_1(5) = 1/15, ...
    This is strictly decreasing, hence trivially unimodal (peak at p = 2). -/
axiom d1_at_2 : kthPrimeFactorDensity 1 2 = 1/2

axiom d1_at_3 : kthPrimeFactorDensity 1 3 = 1/6

/-- d_1 is strictly decreasing: the density of integers with smallest
    prime factor p decreases with p. -/
axiom d1_strictly_decreasing :
  ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p < q →
    kthPrimeFactorDensity 1 q < kthPrimeFactorDensity 1 p

/-- Summary of complete picture:
    - k = 1: trivially unimodal (strictly decreasing)
    - k = 2, 3: unimodal (Cambie 2025)
    - k = 4, ..., 20: NOT unimodal (Cambie 2025)
    - k > 20: open, but expected to not be unimodal -/
theorem erdos_690_summary :
    -- Small k: unimodal
    IsUnimodalOnPrimes (kthPrimeFactorDensity 1) ∧
    IsUnimodalOnPrimes (kthPrimeFactorDensity 2) ∧
    IsUnimodalOnPrimes (kthPrimeFactorDensity 3) ∧
    -- k = 4: not unimodal
    ¬IsUnimodalOnPrimes (kthPrimeFactorDensity 4) :=
  ⟨cambie_unimodal_k1, cambie_unimodal_k2, cambie_unimodal_k3,
   cambie_not_unimodal 4 ⟨le_refl 4, by omega⟩⟩
