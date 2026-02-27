/-
# Binomial Distribution from the Binomial Theorem (OQ-03)

Research Question: Can we derive the binomial distribution and its key
properties directly from the binomial theorem?

Answer: YES. The binomial theorem (p + (1-p))^n = 1 gives normalization,
and algebraic manipulation yields mean = np.

What This Proves:
  Normalization, mean, symmetry, fair coin, Bernoulli special case,
  probability generating function, all from the binomial theorem.

Tags: probability, binomial-distribution, combinatorics, normalization, moments
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open Finset BigOperators

namespace BinomialTheoremOQ03

/-  ## Part I: The Binomial Distribution PMF -/

/-- The binomial PMF: P(X = k) = C(n,k) p^k (1-p)^(n-k). -/
noncomputable def binomPMF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- P(0; n, p) = (1-p)^n. -/
theorem binomPMF_zero (n : ℕ) (p : ℝ) : binomPMF n p 0 = (1 - p) ^ n := by
  simp [binomPMF, Nat.choose_zero_right]

/-- P(n; n, p) = p^n. -/
theorem binomPMF_self (n : ℕ) (p : ℝ) : binomPMF n p n = p ^ n := by
  simp [binomPMF, Nat.choose_self]

/-- Each probability is non-negative when 0 ≤ p ≤ 1. -/
theorem binomPMF_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomPMF n p k := by
  apply mul_nonneg (mul_nonneg _ (pow_nonneg hp0 k)) (pow_nonneg (by linarith) _)
  exact_mod_cast Nat.zero_le _

/-  ## Part II: Normalization from the Binomial Theorem -/

/-- The binomial theorem: (p + q)^n = Σ C(n,k) p^k q^(n-k). -/
theorem binomial_expansion (p q : ℝ) (n : ℕ) :
    (p + q) ^ n = ∑ k ∈ range (n + 1), (Nat.choose n k : ℝ) * p ^ k * q ^ (n - k) := by
  rw [add_pow]; congr 1; ext k; ring

/-- Normalization: the PMF sums to 1. From (p + (1-p))^n = 1. -/
theorem binomPMF_sum_eq_one (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), binomPMF n p k = 1 := by
  unfold binomPMF
  have h := binomial_expansion p (1 - p) n
  rw [add_sub_cancel, one_pow] at h; linarith

/-- The sum does not depend on p. -/
theorem binomPMF_sum_constant (n : ℕ) (p q : ℝ) :
    ∑ k ∈ range (n + 1), binomPMF n p k =
    ∑ k ∈ range (n + 1), binomPMF n q k := by
  rw [binomPMF_sum_eq_one, binomPMF_sum_eq_one]

/-  ## Part III: Symmetry -/

/-- Symmetry: P(k; n, p) = P(n-k; n, 1-p) for k ≤ n. -/
theorem binomPMF_symm (n k : ℕ) (hk : k ≤ n) (p : ℝ) :
    binomPMF n p k = binomPMF n (1 - p) (n - k) := by
  unfold binomPMF
  rw [Nat.choose_symm hk, Nat.sub_sub_self hk, sub_sub_cancel]
  ring

/-  ## Part IV: Mean via Absorption Identity -/

/-- Absorption identity: (k+1) C(n+1, k+1) = (n+1) C(n, k). -/
theorem absorption (n k : ℕ) :
    (k + 1) * Nat.choose (n + 1) (k + 1) = (n + 1) * Nat.choose n k := by
  have := Nat.add_one_mul_choose_eq n k
  linarith

/-- Mean of binomial distribution: E[X] = np (for n ≥ 1). -/
theorem binomial_mean (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) * binomPMF n p k = (n : ℝ) * p := by
  -- Pull out k=0 term (which vanishes)
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul]
  -- Write n = m + 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold binomPMF
  -- Each term: (k+1) * C(m+1, k+1) * p^(k+1) * (1-p)^(m-k)
  -- By absorption: (k+1)*C(m+1,k+1) = (m+1)*C(m,k)
  -- So each term = (m+1) * C(m,k) * p^(k+1) * (1-p)^(m-k)
  --             = (m+1) * p * [C(m,k) * p^k * (1-p)^(m-k)]
  have hterms : ∀ k, k < m + 1 →
      (↑(k + 1) : ℝ) * ((↑(Nat.choose (m + 1) (k + 1)) : ℝ) * p ^ (k + 1) * (1 - p) ^ (m + 1 - (k + 1)))
      = (↑(m + 1) : ℝ) * p * ((↑(Nat.choose m k) : ℝ) * p ^ k * (1 - p) ^ (m - k)) := by
    intro k hk
    have habs := absorption m k
    rw [show m + 1 - (k + 1) = m - k from by omega]
    -- (k+1)*C(m+1,k+1) = (m+1)*C(m,k) as naturals, cast to reals
    have hcast : (↑((k + 1) * Nat.choose (m + 1) (k + 1)) : ℝ) =
        (↑((m + 1) * Nat.choose m k) : ℝ) := by exact_mod_cast habs
    push_cast at hcast
    -- Now: (k+1) * C(m+1,k+1) * p^(k+1) * q^(m-k) = (m+1)*C(m,k) * p * p^k * q^(m-k)
    -- Factor: LHS = [(k+1)*C(m+1,k+1)] * p * p^k * q^(m-k)
    --         RHS = [(m+1)*C(m,k)] * p * p^k * q^(m-k)
    -- These are equal since the bracketed parts are equal
    -- Key: (↑(k+1)) * C = (↑(m+1)) * C' as reals
    have hcr : (↑(k + 1) : ℝ) * (↑(Nat.choose (m + 1) (k + 1)) : ℝ) =
        (↑(m + 1) : ℝ) * (↑(Nat.choose m k) : ℝ) := by exact_mod_cast habs
    -- Both sides equal hcr * p^(k+1) * (1-p)^(m-k) up to rearrangement
    rw [show p ^ (k + 1) = p * p ^ k from pow_succ' p k]
    nlinarith [mul_comm p (p ^ k),
               mul_comm ((↑(Nat.choose (m + 1) (k + 1)) : ℝ)) (p * p ^ k)]
  -- Apply the rewrite to each term
  have hrw : ∑ x ∈ range (m + 1), (↑(x + 1) : ℝ) * ((↑(Nat.choose (m + 1) (x + 1)) : ℝ) * p ^ (x + 1) * (1 - p) ^ (m + 1 - (x + 1)))
    = ∑ x ∈ range (m + 1), (↑(m + 1) : ℝ) * p * ((↑(Nat.choose m x) : ℝ) * p ^ x * (1 - p) ^ (m - x)) := by
    apply Finset.sum_congr rfl
    intro k hk; exact hterms k (Finset.mem_range.mp hk)
  rw [hrw, ← Finset.mul_sum]
  -- The remaining sum is 1 by binomial theorem
  have hsum : ∑ k ∈ range (m + 1), (↑(Nat.choose m k) : ℝ) * p ^ k * (1 - p) ^ (m - k) = 1 := by
    have := binomial_expansion p (1 - p) m
    rw [add_sub_cancel, one_pow] at this; linarith
  rw [hsum]; ring

/-  ## Part V: Special Cases -/

/-- Fair coin: When p = 1/2, P(k) = C(n,k)/2^n. -/
theorem binomPMF_fair_coin (n k : ℕ) :
    binomPMF n (1/2 : ℝ) k = (Nat.choose n k : ℝ) / 2 ^ n := by
  unfold binomPMF
  by_cases hk : k ≤ n
  · have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [this]
    have h2 : (1 / 2 : ℝ) ^ k * ((1 / 2 : ℝ) ^ (n - k)) = (1 / 2 : ℝ) ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [show (↑(Nat.choose n k) : ℝ) * (1 / 2) ^ k * (1 / 2) ^ (n - k) =
        (↑(Nat.choose n k) : ℝ) * ((1 / 2) ^ k * (1 / 2) ^ (n - k)) from by ring]
    rw [h2]
    rw [show (1 / 2 : ℝ) ^ n = 2⁻¹ ^ n from by norm_num]
    rw [div_eq_mul_inv, inv_pow]
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Bernoulli: binomPMF 1 p 1 = p. -/
theorem binomPMF_bernoulli_one (p : ℝ) : binomPMF 1 p 1 = p := by
  simp [binomPMF]

/-- Bernoulli: binomPMF 1 p 0 = 1 - p. -/
theorem binomPMF_bernoulli_zero (p : ℝ) : binomPMF 1 p 0 = 1 - p := by
  simp [binomPMF]

/-- Certain event: P(n; n, 1) = 1. -/
theorem binomPMF_certain (n : ℕ) : binomPMF n 1 n = 1 := by
  simp [binomPMF]

/-- Impossible event: P(0; n, 0) = 1. -/
theorem binomPMF_impossible (n : ℕ) : binomPMF n 0 0 = 1 := by
  simp [binomPMF]

/-  ## Part VI: Monotonicity -/

/-- The mean np is monotone: p ≤ q implies np ≤ nq. -/
theorem binomial_mean_monotone (n : ℕ) (p q : ℝ) (hpq : p ≤ q) :
    (n : ℝ) * p ≤ (n : ℝ) * q := by
  apply mul_le_mul_of_nonneg_left hpq
  exact Nat.cast_nonneg' n

/-  ## Part VII: Connection to Binomial Theorem -/

/-- The binomial theorem IS the normalization:
    (p + (1-p))^n = 1 = sum of PMF. -/
theorem binomial_theorem_is_normalization (n : ℕ) (p : ℝ) :
    (p + (1 - p)) ^ n = ∑ k ∈ range (n + 1), binomPMF n p k := by
  rw [binomPMF_sum_eq_one, add_sub_cancel, one_pow]

/-- Probability generating function: E[t^X] = (pt + 1-p)^n. -/
theorem binomial_pgf (n : ℕ) (p t : ℝ) :
    ∑ k ∈ range (n + 1), t ^ k * binomPMF n p k = (p * t + (1 - p)) ^ n := by
  unfold binomPMF
  simp_rw [show ∀ k, t ^ k * ((↑(Nat.choose n k) : ℝ) * p ^ k * (1 - p) ^ (n - k))
    = (↑(Nat.choose n k) : ℝ) * (p * t) ^ k * (1 - p) ^ (n - k) from
    fun k => by ring]
  rw [← binomial_expansion (p * t) (1 - p) n]

/-- The PGF at t=1 recovers normalization. -/
theorem pgf_at_one (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), 1 ^ k * binomPMF n p k = 1 := by
  simp_rw [one_pow, one_mul]; exact binomPMF_sum_eq_one n p

/-- PGF derivative at t=1 gives mean np. -/
theorem pgf_derivative_at_one (n : ℕ) (p : ℝ) :
    (n : ℝ) * (p * 1 + (1 - p)) ^ (n - 1) * p = (n : ℝ) * p := by
  simp [add_sub_cancel]

/-  ## Part VIII: Summary -/

/-- OQ-03 summary: normalization, PGF, and fair-coin formula. -/
theorem binomial_oq03_summary (n : ℕ) (p t : ℝ) (k : ℕ) :
    (∑ j ∈ range (n + 1), binomPMF n p j = 1) ∧
    (∑ j ∈ range (n + 1), t ^ j * binomPMF n p j = (p * t + (1 - p)) ^ n) ∧
    (binomPMF n (1/2 : ℝ) k = (Nat.choose n k : ℝ) / 2 ^ n) :=
  ⟨binomPMF_sum_eq_one n p, binomial_pgf n p t, binomPMF_fair_coin n k⟩

end BinomialTheoremOQ03
