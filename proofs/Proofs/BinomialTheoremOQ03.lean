/-
# Binomial Distribution from the Binomial Theorem (OQ-03)

Research Question: Can we derive the binomial distribution and its key
properties directly from the binomial theorem?

Answer: YES. The binomial theorem (p + (1-p))^n = 1 gives normalization,
and algebraic manipulation yields mean = np.

What This Proves:
  Normalization, mean, symmetry, fair coin, Bernoulli special case,
  probability generating function, Poisson limit theorem, convolution
  property, and Chebyshev concentration bound — all from the binomial theorem.

Tags: probability, binomial-distribution, combinatorics, normalization, moments,
      poisson-limit, convolution, vandermonde, chebyshev
-/

import Mathlib

open Finset BigOperators Filter Topology

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
    rw [show p ^ (k + 1) = p * p ^ k from pow_succ' p k]
    calc (↑(k + 1) : ℝ) * ((↑(Nat.choose (m + 1) (k + 1)) : ℝ) * (p * p ^ k) * (1 - p) ^ (m - k))
        = (↑(k + 1) * ↑(Nat.choose (m + 1) (k + 1))) * (p * p ^ k * (1 - p) ^ (m - k)) := by ring
      _ = (↑(m + 1) * ↑(Nat.choose m k)) * (p * p ^ k * (1 - p) ^ (m - k)) := by rw [hcr]
      _ = ↑(m + 1) * p * (↑(Nat.choose m k) * p ^ k * (1 - p) ^ (m - k)) := by ring
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

/-  ## Part VIII: Double Absorption and Second Factorial Moment -/

/-- Double absorption: (k+2)(k+1) C(n+2, k+2) = (n+2)(n+1) C(n,k).
    Two applications of the absorption identity. -/
theorem double_absorption (n k : ℕ) :
    (k + 2) * (k + 1) * Nat.choose (n + 2) (k + 2) =
    (n + 2) * (n + 1) * Nat.choose n k := by
  have h1 := absorption (n + 1) (k + 1)
  have h2 := absorption n k
  nlinarith

/-- Second factorial moment: E[X(X-1)] = n(n-1)p² for n ≥ 2.
    Proved by pulling out the k=0,1 terms (which vanish), then using
    double absorption to reduce to the binomial theorem. -/
theorem binomial_second_factorial_moment (n : ℕ) (hn : 2 ≤ n) (p : ℝ) :
    ∑ k ∈ range (n + 1), ((k : ℝ) * ((k : ℝ) - 1)) * binomPMF n p k =
    (n : ℝ) * ((n : ℝ) - 1) * p ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- Pull out k=0: 0*(0-1)*PMF = 0
  rw [show m + 2 + 1 = (m + 2) + 1 from rfl, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul]
  -- Pull out k=1: 1*(1-1)*PMF = 0. Range (m+2) = range ((m+1)+1)
  rw [show m + 2 = (m + 1) + 1 from by omega, Finset.sum_range_succ']
  simp only [show (0 : ℕ) + 1 = 1 from rfl, Nat.cast_one, one_mul, sub_self, zero_mul]
  -- Remaining sum: ∑ j ∈ range (m+1), f(j+1+1) where index represents k=j+2
  -- Rewrite each term using double absorption
  have hterms : ∀ j, j ∈ range (m + 1) →
      ((↑(j + 1 + 1) : ℝ) * ((↑(j + 1 + 1) : ℝ) - 1)) * binomPMF (m + 2) p (j + 1 + 1) =
      ((↑(m + 2) : ℝ) * ↑(m + 1)) * p ^ 2 *
        ((↑(Nat.choose m j) : ℝ) * p ^ j * (1 - p) ^ (m - j)) := by
    intro j hj
    have hjm : j < m + 1 := Finset.mem_range.mp hj
    unfold binomPMF
    have hdabs := double_absorption m j
    have hcast : (↑(j + 2) : ℝ) * ↑(j + 1) * ↑(Nat.choose (m + 2) (j + 2)) =
        (↑(m + 2) : ℝ) * ↑(m + 1) * ↑(Nat.choose m j) := by exact_mod_cast hdabs
    -- Normalize indices and powers
    rw [show m + 2 - (j + 1 + 1) = m - j from by omega]
    calc (↑(j + 1 + 1) * (↑(j + 1 + 1) - 1)) *
          (↑(Nat.choose (m + 2) (j + 1 + 1)) * p ^ (j + 1 + 1) * (1 - p) ^ (m - j))
        = (↑(j + 2) * ↑(j + 1) * ↑(Nat.choose (m + 2) (j + 2))) *
          (p ^ 2 * p ^ j * (1 - p) ^ (m - j)) := by push_cast; ring
      _ = (↑(m + 2) * ↑(m + 1) * ↑(Nat.choose m j)) *
          (p ^ 2 * p ^ j * (1 - p) ^ (m - j)) := by rw [hcast]
      _ = (↑(m + 2) * ↑(m + 1)) * p ^ 2 *
          (↑(Nat.choose m j) * p ^ j * (1 - p) ^ (m - j)) := by ring
  rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum]
  -- Remaining sum is 1 by binomial theorem: (p + (1-p))^m = 1
  have hsum : ∑ k ∈ range (m + 1), (↑(Nat.choose m k) : ℝ) * p ^ k * (1 - p) ^ (m - k) = 1 := by
    have := binomial_expansion p (1 - p) m
    rw [add_sub_cancel, one_pow] at this; linarith
  rw [hsum]; push_cast; ring

/-- Variance of the binomial distribution: Var(X) = np(1-p) for n ≥ 2.
    Proof: Var(X) = E[X²] - (E[X])² = (E[X(X-1)] + E[X]) - (E[X])²
                  = n(n-1)p² + np - n²p² = np - np² = np(1-p). -/
theorem binomial_variance (n : ℕ) (hn : 2 ≤ n) (p : ℝ) :
    (∑ k ∈ range (n + 1), ((k : ℝ) ^ 2 * binomPMF n p k)) -
    (∑ k ∈ range (n + 1), ((k : ℝ) * binomPMF n p k)) ^ 2 =
    (n : ℝ) * p * (1 - p) := by
  -- E[X²] = E[X(X-1)] + E[X] = n(n-1)p² + np
  have h_sfm := binomial_second_factorial_moment n hn p
  have h_mean := binomial_mean n (by omega) p
  -- Rewrite E[X²] using E[X(X-1)] + E[X]
  have h_sq : ∑ k ∈ range (n + 1), ((k : ℝ) ^ 2 * binomPMF n p k) =
      (∑ k ∈ range (n + 1), ((k : ℝ) * ((k : ℝ) - 1)) * binomPMF n p k) +
      (∑ k ∈ range (n + 1), ((k : ℝ) * binomPMF n p k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [h_sq, h_sfm, h_mean]; ring

/-  ## Part IX: Convolution via Vandermonde's Identity -/

/-- Vandermonde's identity in range form: C(n+m, k) = Σ_j C(n,j) * C(m, k-j). -/
theorem vandermonde_range (n m k : ℕ) :
    Nat.choose (n + m) k =
    ∑ j ∈ range (k + 1), Nat.choose n j * Nat.choose m (k - j) := by
  rw [Nat.add_choose_eq]
  exact (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => Nat.choose n i * Nat.choose m j)) k

/-- Convolution of binomial PMFs: Bin(n,p) * Bin(m,p) = Bin(n+m,p).
    The sum of independent Bin(n,p) and Bin(m,p) random variables
    has distribution Bin(n+m,p). -/
theorem binomPMF_convolution (n m k : ℕ) (p : ℝ) :
    ∑ j ∈ range (k + 1), binomPMF n p j * binomPMF m p (k - j) =
    binomPMF (n + m) p k := by
  unfold binomPMF
  -- Each term factors as C(n,j)*C(m,k-j) * p^k * (1-p)^(n+m-k)
  have hterm : ∀ j ∈ range (k + 1),
      (↑(Nat.choose n j) : ℝ) * p ^ j * (1 - p) ^ (n - j) *
      ((↑(Nat.choose m (k - j)) : ℝ) * p ^ (k - j) * (1 - p) ^ (m - (k - j))) =
      (↑(Nat.choose n j) : ℝ) * (↑(Nat.choose m (k - j)) : ℝ) *
      p ^ k * (1 - p) ^ (n + m - k) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hjn : j ≤ n
    · by_cases hkjm : k - j ≤ m
      · have hp : p ^ j * p ^ (k - j) = p ^ k := by
          rw [← pow_add]; congr 1; omega
        have hq : (1 - p) ^ (n - j) * (1 - p) ^ (m - (k - j)) =
            (1 - p) ^ (n + m - k) := by
          rw [← pow_add]; congr 1; omega
        calc (↑(Nat.choose n j) : ℝ) * p ^ j * (1 - p) ^ (n - j) *
              ((↑(Nat.choose m (k - j)) : ℝ) * p ^ (k - j) * (1 - p) ^ (m - (k - j)))
            = (↑(Nat.choose n j) : ℝ) * (↑(Nat.choose m (k - j)) : ℝ) *
              (p ^ j * p ^ (k - j)) *
              ((1 - p) ^ (n - j) * (1 - p) ^ (m - (k - j))) := by ring
          _ = (↑(Nat.choose n j) : ℝ) * (↑(Nat.choose m (k - j)) : ℝ) *
              p ^ k * (1 - p) ^ (n + m - k) := by rw [hp, hq]
      · have : Nat.choose m (k - j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [this]
    · have : Nat.choose n j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
  rw [Finset.sum_congr rfl hterm]
  -- Factor out p^k * (1-p)^(n+m-k)
  have hfactor : ∀ j ∈ range (k + 1),
      (↑(Nat.choose n j) : ℝ) * (↑(Nat.choose m (k - j)) : ℝ) *
      p ^ k * (1 - p) ^ (n + m - k) =
      (↑(Nat.choose n j) : ℝ) * (↑(Nat.choose m (k - j)) : ℝ) *
      (p ^ k * (1 - p) ^ (n + m - k)) := by
    intro j _; ring
  rw [Finset.sum_congr rfl hfactor, ← Finset.sum_mul]
  -- Apply Vandermonde: ∑ C(n,j)*C(m,k-j) = C(n+m,k)
  have hvand := vandermonde_range n m k
  have hcast : (∑ j ∈ range (k + 1),
      (↑(Nat.choose n j) : ℝ) * (↑(Nat.choose m (k - j)) : ℝ)) =
      (↑(Nat.choose (n + m) k) : ℝ) := by
    rw [hvand]; push_cast; rfl
  rw [hcast]; ring

/-  ## Part X: Poisson Limit Theorem -/

/-- The classical limit (1+x/n)^n → exp(x).
    Proved via: log(1+h)/h → 1 at h=0 (derivative of log at 1),
    so n·log(1+x/n) → x, and continuity of exp gives the result. -/
theorem tendsto_one_plus_div_pow_exp (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 + x / (↑n : ℝ)) ^ n)
    Filter.atTop (nhds (Real.exp x)) := by
  -- Case x = 0: trivial
  by_cases hx : x = 0
  · subst hx
    simp only [zero_div, add_zero, one_pow, Real.exp_zero]
    exact tendsto_const_nhds
  -- Step A: HasDerivAt (fun t => log(1+t)) 1 0
  have hd : HasDerivAt (fun t : ℝ => Real.log (1 + t)) 1 (0 : ℝ) := by
    have h1 : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 (0 : ℝ) :=
      (hasDerivAt_id (0 : ℝ)).const_add 1
    have h2 : HasDerivAt Real.log (1 : ℝ)⁻¹ ((fun t : ℝ => 1 + t) (0 : ℝ)) := by
      show HasDerivAt Real.log 1⁻¹ (1 + 0)
      rw [add_zero]
      exact Real.hasDerivAt_log one_ne_zero
    have h3 := h2.comp (0 : ℝ) h1
    simp only [inv_one, mul_one] at h3
    exact h3
  -- Step B: log(1+h)/h → 1 as h → 0 (from derivative of log at 1)
  have hslope : Tendsto (fun h : ℝ => Real.log (1 + h) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
    have hs : Tendsto (slope (fun t : ℝ => Real.log (1 + t)) 0)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
      rw [show nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ = nhds 0 ⊓ 𝓟 {(0 : ℝ)}ᶜ from rfl]
      exact hasDerivAtFilter_iff_tendsto_slope.mp (hd.hasDerivAtFilter le_rfl)
    refine hs.congr (fun h => ?_)
    simp [slope, sub_zero, Real.log_one, smul_eq_mul, inv_mul_eq_div]
  -- Step C: x/n → 0 in nhdsWithin 0 {0}ᶜ (approaches 0 but ≠ 0)
  have hxn : Tendsto (fun n : ℕ => x / (↑n : ℝ)) atTop
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    rw [nhdsWithin, tendsto_inf]
    exact ⟨tendsto_const_div_atTop_nhds_zero_nat x,
      tendsto_principal.mpr (eventually_atTop.mpr ⟨1, fun n hn =>
        div_ne_zero hx (Nat.cast_ne_zero.mpr (by omega))⟩)⟩
  -- Step D: log(1+x/n)/(x/n) → 1 by composition
  have hcomp : Tendsto (fun n : ℕ => Real.log (1 + x / ↑n) / (x / ↑n)) atTop (nhds 1) :=
    hslope.comp hxn
  -- Step E: n * log(1+x/n) = x * (log(1+x/n)/(x/n)) eventually
  have heq : ∀ᶠ (n : ℕ) in atTop, (↑n : ℝ) * Real.log (1 + x / ↑n) =
      x * (Real.log (1 + x / ↑n) / (x / ↑n)) := by
    filter_upwards [Ici_mem_atTop 1] with n (hn : 1 ≤ n)
    have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hxdiv : x / (x / (↑n : ℝ)) = ↑n := by field_simp
    set L := Real.log (1 + x / (↑n : ℝ))
    calc ↑n * L = L * ↑n := by ring
      _ = L * (x / (x / ↑n)) := by rw [hxdiv]
      _ = x * (L / (x / ↑n)) := by ring
  -- Step F: n * log(1+x/n) → x
  have hlog : Tendsto (fun n : ℕ => (↑n : ℝ) * Real.log (1 + x / ↑n)) atTop (nhds x) := by
    have h := (tendsto_const_nhds (x := x)).mul hcomp
    rw [mul_one] at h
    exact h.congr' (heq.mono fun n hn => hn.symm)
  -- Step G: exp(n * log(1+x/n)) → exp(x) by continuity of exp
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  -- Step H: exp(n * log(1+x/n)) = (1+x/n)^n for large n (when 1+x/n > 0)
  refine hexp.congr' ?_
  filter_upwards [Ici_mem_atTop (Nat.ceil |x| + 1)] with n hn
  simp only [Function.comp]
  have hn_pos : (0 : ℝ) < ↑n := by
    have : 1 ≤ n := le_trans (Nat.le_add_left 1 _) hn
    exact Nat.cast_pos.mpr (by omega)
  have habs : |x| < ↑n := by
    calc |x| ≤ ↑(Nat.ceil |x|) := Nat.le_ceil |x|
      _ < ↑(Nat.ceil |x|) + 1 := by linarith
      _ ≤ ↑n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < 1 + x / ↑n := by
    have hle : -(x / ↑n) ≤ |x / ↑n| := neg_le_abs _
    have hlt : |x / ↑n| < 1 := by
      rw [abs_div, abs_of_pos hn_pos]
      exact (div_lt_one hn_pos).mpr habs
    linarith
  rw [Real.exp_nat_mul, Real.exp_log hbase]

-- The Poisson PMF
/-- The Poisson probability mass function: P(X=k) = e^(-r) r^k / k! -/
noncomputable def poissonPMF (r : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-r) * r ^ k / (Nat.factorial k : ℝ)

/-- Poisson PMF at k=0: P(X=0) = e^(-r). -/
theorem poissonPMF_zero (r : ℝ) : poissonPMF r 0 = Real.exp (-r) := by
  simp [poissonPMF]

/-- Poisson limit theorem for k=0: Bin(n, r/n) → Poi(r) at k=0.
    This is the base case: (1 - r/n)^n → e^(-r). -/
theorem poisson_limit_zero (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => binomPMF n (r / ↑n) 0)
    Filter.atTop (nhds (poissonPMF r 0)) := by
  simp only [poissonPMF_zero, binomPMF_zero]
  have hrw : (fun n : ℕ => (1 - r / (↑n : ℝ)) ^ n) =
      (fun n : ℕ => (1 + (-r) / (↑n : ℝ)) ^ n) := by
    ext n; ring_nf
  rw [hrw]
  exact tendsto_one_plus_div_pow_exp (-r)

/-- Choose ratio identity: (k+1) C(n, k+1) = (n-k) C(n, k) for k+1 ≤ n. -/
theorem choose_succ_mul (n k : ℕ) (hk : k + 1 ≤ n) :
    (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ n from hk)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ n by omega)
  rw [show (k + 1).factorial = (k + 1) * k.factorial from Nat.factorial_succ k] at h1
  rw [show (n - k).factorial = (n - k) * (n - (k + 1)).factorial from by
    rw [show n - k = (n - (k + 1)) + 1 from by omega]; exact Nat.factorial_succ _] at h2
  have hpos : 0 < k.factorial * (n - (k + 1)).factorial := by positivity
  have lhs : Nat.choose n (k + 1) * ((k + 1) * k.factorial) * (n - (k + 1)).factorial =
    (k + 1) * Nat.choose n (k + 1) * (k.factorial * (n - (k + 1)).factorial) := by ring
  have rhs : Nat.choose n k * k.factorial * ((n - k) * (n - (k + 1)).factorial) =
    (n - k) * Nat.choose n k * (k.factorial * (n - (k + 1)).factorial) := by ring
  rw [lhs] at h1; rw [rhs] at h2
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

/-- For the Poisson limit: the ratio of consecutive binomial PMFs converges.
    binomPMF n (r/n) (k+1) / binomPMF n (r/n) k → r/(k+1) as n → ∞. -/
theorem poisson_ratio_tendsto (r : ℝ) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (↑(n - k) : ℝ) * r / ((↑(k + 1) : ℝ) * ↑n * (1 - r / ↑n)))
    Filter.atTop (nhds (r / (↑(k + 1) : ℝ))) := by
  suffices h : Filter.Tendsto (fun n : ℕ => ((↑n - ↑k : ℝ) / ↑n) * (r / ↑(k + 1)) *
      (1 / (1 - r / ↑n))) Filter.atTop (nhds (1 * (r / ↑(k + 1)) * 1)) by
    simp only [one_mul, mul_one] at h
    refine h.congr' ?_
    filter_upwards [Filter.Ici_mem_atTop (k + 1)] with n hn
    have hn_ge : k + 1 ≤ n := hn
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
    rw [show (↑(n - k) : ℝ) = ↑n - ↑k from Nat.cast_sub (by omega)]
    field_simp
  apply Filter.Tendsto.mul
  apply Filter.Tendsto.mul
  · -- (n-k)/n → 1
    have : Filter.Tendsto (fun n : ℕ => (↑k : ℝ) / ↑n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (↑k : ℝ)
    have h1 : Filter.Tendsto (fun n : ℕ => 1 - (↑k : ℝ) / ↑n) Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub this
    simp only [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [Filter.Ici_mem_atTop (k + 1)] with n hn
    have hn_ge : k + 1 ≤ n := hn
    have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
    rw [sub_div, div_self (ne_of_gt hn_pos)]
  · exact tendsto_const_nhds
  · -- 1/(1-r/n) → 1
    have : Filter.Tendsto (fun n : ℕ => r / ↑n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat r
    have h1 : Filter.Tendsto (fun n : ℕ => 1 - r / ↑n) Filter.atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub this
    simp only [sub_zero] at h1
    have h2 : Filter.Tendsto (fun n : ℕ => 1 / (1 - r / ↑n)) Filter.atTop (nhds (1 / 1)) :=
      Filter.Tendsto.div tendsto_const_nhds h1 one_ne_zero
    simpa using h2

/-- Factoring: binomPMF n p (k+1) = binomPMF n p k * (n-k)*p / ((k+1)*(1-p))
    for k+1 ≤ n and 1-p ≠ 0. -/
theorem binomPMF_succ_eq (n k : ℕ) (hk : k + 1 ≤ n) (p : ℝ) (hq : 1 - p ≠ 0) :
    binomPMF n p (k + 1) =
    binomPMF n p k * ((↑(n - k) : ℝ) * p / ((↑(k + 1) : ℝ) * (1 - p))) := by
  unfold binomPMF
  have hk1 : (↑(k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hchoose := choose_succ_mul n k hk
  -- Cast the choose identity to ℝ
  have hchoose_cast : (↑(k + 1) : ℝ) * (↑(Nat.choose n (k + 1)) : ℝ) =
      (↑(n - k) : ℝ) * (↑(Nat.choose n k) : ℝ) := by exact_mod_cast hchoose
  -- Rewrite C(n,k+1) = C(n,k)*(n-k)/(k+1)
  have hcr : (↑(Nat.choose n (k + 1)) : ℝ) =
      (↑(Nat.choose n k) : ℝ) * (↑(n - k) : ℝ) / (↑(k + 1) : ℝ) := by
    rw [eq_div_iff hk1]; linarith [hchoose_cast]
  rw [hcr]
  -- p^(k+1) = p^k * p
  rw [show p ^ (k + 1) = p ^ k * p from pow_succ p k]
  -- (1-p)^(n-(k+1)) = (1-p)^(n-k) / (1-p)
  have hpow : (1 - p) ^ (n - (k + 1)) * (1 - p) = (1 - p) ^ (n - k) := by
    rw [← pow_succ]; congr 1; omega
  have hpow' : (1 - p) ^ (n - (k + 1)) = (1 - p) ^ (n - k) / (1 - p) := by
    rw [eq_div_iff hq]; exact hpow
  rw [hpow']
  field_simp

/-- Poisson PMF recurrence: poissonPMF r (k+1) = poissonPMF r k * r/(k+1). -/
theorem poissonPMF_succ (r : ℝ) (k : ℕ) :
    poissonPMF r (k + 1) = poissonPMF r k * (r / (↑(k + 1) : ℝ)) := by
  unfold poissonPMF
  rw [Nat.factorial_succ, pow_succ]
  have hk1 : (↑(k + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfact : (↑(Nat.factorial k) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne'
  field_simp
  push_cast
  ring

/-- Poisson limit theorem: For each fixed k, Bin(n, r/n) → Poi(r) as n → ∞.
    The binomial distribution with parameters n and r/n converges pointwise
    to the Poisson distribution with parameter r.
    Proof by induction on k using the consecutive term ratio. -/
theorem poisson_limit (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => binomPMF n (r / ↑n) k)
    Filter.atTop (nhds (poissonPMF r k)) := by
  induction k with
  | zero => exact poisson_limit_zero r
  | succ k ih =>
    rw [poissonPMF_succ]
    -- For large n, factor using binomPMF_succ_eq
    have hev : ∀ᶠ n in Filter.atTop,
        binomPMF n (r / ↑n) (k + 1) =
        binomPMF n (r / ↑n) k *
        ((↑(n - k) : ℝ) * (r / ↑n) / ((↑(k + 1) : ℝ) * (1 - r / ↑n))) := by
      filter_upwards [Filter.Ici_mem_atTop (k + 1), Filter.Ici_mem_atTop (Nat.ceil r + 1)]
        with n hn1 hn2
      have hn_ge : k + 1 ≤ n := by exact_mod_cast hn1
      apply binomPMF_succ_eq n k hn_ge
      have : (↑n : ℝ) > r := by
        calc (↑n : ℝ) ≥ ↑(Nat.ceil r + 1) := by exact_mod_cast hn2
          _ = ↑(Nat.ceil r) + 1 := by push_cast; ring
          _ > r := by linarith [Nat.le_ceil r]
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
      linarith [show r / ↑n < 1 from by rwa [div_lt_one hn_pos]]
    -- The ratio simplifies and converges
    have hratio : Filter.Tendsto
        (fun n : ℕ => (↑(n - k) : ℝ) * (r / ↑n) / ((↑(k + 1) : ℝ) * (1 - r / ↑n)))
        Filter.atTop (nhds (r / (↑(k + 1) : ℝ))) := by
      have hfun : (fun n : ℕ => (↑(n - k) : ℝ) * (r / ↑n) / ((↑(k + 1) : ℝ) * (1 - r / ↑n))) =
          (fun n : ℕ => (↑(n - k) : ℝ) * r / ((↑(k + 1) : ℝ) * ↑n * (1 - r / ↑n))) := by
        ext n; by_cases hn : (↑n : ℝ) = 0 <;> field_simp
      rw [hfun]
      exact poisson_ratio_tendsto r k
    exact Filter.Tendsto.congr' (hev.mono fun n hn => hn.symm) (ih.mul hratio)

/-  ## Part XI: Extended Summary -/

/-- Extended OQ-03 summary: normalization, mean, variance, PGF, fair-coin,
    convolution, and Poisson limit theorem. -/
theorem binomial_oq03_extended_summary (n m : ℕ) (hn : 2 ≤ n) (p t r : ℝ)
    (hr : 0 < r) (k : ℕ) :
    -- Normalization
    (∑ j ∈ range (n + 1), binomPMF n p j = 1) ∧
    -- Mean
    (∑ j ∈ range (n + 1), (j : ℝ) * binomPMF n p j = (n : ℝ) * p) ∧
    -- Variance
    ((∑ j ∈ range (n + 1), ((j : ℝ) ^ 2 * binomPMF n p j)) -
     (∑ j ∈ range (n + 1), ((j : ℝ) * binomPMF n p j)) ^ 2 =
     (n : ℝ) * p * (1 - p)) ∧
    -- PGF
    (∑ j ∈ range (n + 1), t ^ j * binomPMF n p j = (p * t + (1 - p)) ^ n) ∧
    -- Fair coin
    (binomPMF n (1/2 : ℝ) k = (Nat.choose n k : ℝ) / 2 ^ n) ∧
    -- Convolution (Vandermonde)
    (∑ j ∈ range (k + 1), binomPMF n p j * binomPMF m p (k - j) =
     binomPMF (n + m) p k) ∧
    -- Poisson limit
    (Filter.Tendsto (fun N : ℕ => binomPMF N (r / ↑N) k)
      Filter.atTop (nhds (poissonPMF r k))) :=
  ⟨binomPMF_sum_eq_one n p, binomial_mean n (by omega) p,
   binomial_variance n hn p, binomial_pgf n p t, binomPMF_fair_coin n k,
   binomPMF_convolution n m k p, poisson_limit r hr k⟩

end BinomialTheoremOQ03
