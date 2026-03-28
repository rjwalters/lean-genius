/-
# Erdős Problem 462: Least Prime Factor Sums in Short Intervals

Let `p(n)` denote the least prime factor of `n`. There exists `c > 0`
such that `∑_{n<x, n composite} p(n)/n ~ c · x^{1/2} / (log x)²`.

Does there exist `C > 0` such that
`∑_{x ≤ n ≤ x + C·x^{1/2}·(log x)²} p(n)/n ≫ 1`
for all sufficiently large `x`?

*Reference:* [erdosproblems.com/462](https://www.erdosproblems.com/462),
Erdős–Graham (1980), p. 92.
-/

import Mathlib

/- ## Least prime factor -/

/-- The least prime factor of `n` (returns 0 for `n ≤ 1`). -/
noncomputable def leastPrimeFactor (n : ℕ) : ℕ :=
    if h : n ≤ 1 then 0
    else n.minFac

/-- For `n ≥ 2`, `leastPrimeFactor n` is prime. -/
theorem leastPrimeFactor_prime (n : ℕ) (hn : 2 ≤ n) :
    (leastPrimeFactor n).Prime := by
  unfold leastPrimeFactor; rw [dif_neg (by omega)]
  exact Nat.minFac_prime (by omega)

/-- `leastPrimeFactor n` divides `n` for `n ≥ 2`. -/
theorem leastPrimeFactor_dvd (n : ℕ) (hn : 2 ≤ n) :
    leastPrimeFactor n ∣ n := by
  unfold leastPrimeFactor; rw [dif_neg (by omega)]
  exact Nat.minFac_dvd n

/-- `leastPrimeFactor n` is at most any prime dividing `n`. -/
theorem leastPrimeFactor_le (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) :
    leastPrimeFactor n ≤ p := by
  unfold leastPrimeFactor; rw [dif_neg (by omega)]
  exact Nat.minFac_le_of_dvd hp.two_le hpn

/- ## Sums involving least prime factor -/

/-- Sum of `p(n)/n` over composites in `{2, …, x-1}`. -/
noncomputable def compositeSum (x : ℕ) : ℝ :=
    (Finset.Icc 2 (x - 1)).sum fun n =>
      if n.Prime then 0
      else (leastPrimeFactor n : ℝ) / (n : ℝ)

/-- Sum of `p(n)/n` over an interval `{a, …, b}`. -/
noncomputable def intervalSum (a b : ℕ) : ℝ :=
    (Finset.Icc a b).sum fun n =>
      (leastPrimeFactor n : ℝ) / (n : ℝ)

/- ## Known asymptotics -/

/-- There exists `c > 0` such that `∑_{n<x, composite} p(n)/n ~ c·√x/(log x)²`.
We state a one-sided bound: the sum is `Θ(√x/(log x)²)`. -/
axiom compositeSum_asymptotic :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        c₁ * (x : ℝ) ^ (1/2 : ℝ) / (Real.log x) ^ 2 ≤ compositeSum x ∧
        compositeSum x ≤ c₂ * (x : ℝ) ^ (1/2 : ℝ) / (Real.log x) ^ 2

/- ## Main conjecture -/

/-- Erdős Problem 462: There exists `C > 0` such that the sum
`∑_{x ≤ n ≤ x + C·√x·(log x)²} p(n)/n` is bounded below by
an absolute constant for all large `x`. -/
def ErdosProblem462 : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
          δ ≤ intervalSum x ⌊(x : ℝ) + C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log x) ^ 2⌋₊

/- ## Basic properties -/

/-- The least prime factor of a prime is itself. -/
theorem leastPrimeFactor_prime_self (p : ℕ) (hp : p.Prime) :
    leastPrimeFactor p = p := by
  unfold leastPrimeFactor
  have := hp.two_le
  rw [dif_neg (by omega)]
  exact hp.minFac_eq

/-- The least prime factor of any `n ≥ 2` is at least 2. -/
theorem leastPrimeFactor_ge_two (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ leastPrimeFactor n := by
  unfold leastPrimeFactor; rw [dif_neg (by omega)]
  exact (Nat.minFac_prime (by omega : n ≠ 1)).two_le

/-- The least prime factor of any `n ≥ 2` is at most `√n` for composite `n`. -/
theorem leastPrimeFactor_le_sqrt (n : ℕ) (hn : 2 ≤ n) (hc : ¬n.Prime) :
    (leastPrimeFactor n : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ) := by
  unfold leastPrimeFactor; rw [dif_neg (by omega)]
  have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hc
  suffices h : (n.minFac : ℝ) ≤ Real.sqrt (n : ℝ) by
    rwa [Real.sqrt_eq_rpow] at h
  rw [← Real.sqrt_sq (Nat.cast_nonneg (n.minFac))]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hsq)

/- ## Sum properties -/

/-- The composite sum is non-negative. -/
theorem compositeSum_nonneg (x : ℕ) : 0 ≤ compositeSum x := by
  unfold compositeSum
  apply Finset.sum_nonneg
  intro n _
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The composite sum is monotonically non-decreasing. -/
theorem compositeSum_mono {x y : ℕ} (hxy : x ≤ y) : compositeSum x ≤ compositeSum y := by
  unfold compositeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn; simp only [Finset.mem_Icc] at *; omega
  · intro n _ _
    split_ifs with h
    · exact le_refl 0
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The interval sum is non-negative. -/
theorem intervalSum_nonneg (a b : ℕ) : 0 ≤ intervalSum a b := by
  unfold intervalSum
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/- ## Additional structural properties -/

/-- The least prime factor of `n ≥ 2` is at most `n`. -/
theorem leastPrimeFactor_le_self (n : ℕ) (hn : 2 ≤ n) :
    leastPrimeFactor n ≤ n := by
  have hdvd := leastPrimeFactor_dvd n hn
  exact Nat.le_of_dvd (by omega) hdvd

/-- For even `n ≥ 2`, the least prime factor is 2. -/
theorem leastPrimeFactor_even (n : ℕ) (hn : 2 ≤ n) (heven : 2 ∣ n) :
    leastPrimeFactor n = 2 := by
  have hge := leastPrimeFactor_ge_two n hn
  have hle := leastPrimeFactor_le n 2 hn Nat.prime_two heven
  omega

/-- Each term `p(n)/n` in the interval sum is at most 1 for `n ≥ 2`. -/
theorem leastPrimeFactor_div_le_one (n : ℕ) (hn : 2 ≤ n) :
    (leastPrimeFactor n : ℝ) / (n : ℝ) ≤ 1 := by
  rw [div_le_one (Nat.cast_pos.mpr (by omega))]
  exact Nat.cast_le.mpr (leastPrimeFactor_le_self n hn)

/-- Enlarging the interval increases the sum (all terms non-negative). -/
theorem intervalSum_mono {a₁ b₁ a₂ b₂ : ℕ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    intervalSum a₁ b₁ ≤ intervalSum a₂ b₂ := by
  unfold intervalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn; simp only [Finset.mem_Icc] at *; omega
  · intro n _ _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The interval sum over a single point `{n}`. -/
theorem intervalSum_singleton (n : ℕ) :
    intervalSum n n = (leastPrimeFactor n : ℝ) / (n : ℝ) := by
  unfold intervalSum
  simp [Finset.Icc_self]

/-- Splitting an interval sum at a midpoint. -/
theorem intervalSum_split (a m b : ℕ) (ham : a ≤ m + 1) (hmb : m + 1 ≤ b) :
    intervalSum a b = intervalSum a m + intervalSum (m + 1) b := by
  unfold intervalSum
  have hdisj : Disjoint (Finset.Icc a m) (Finset.Icc (m + 1) b) := by
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂; simp only [Finset.mem_Icc] at *; omega
  have hunion : Finset.Icc a m ∪ Finset.Icc (m + 1) b = Finset.Icc a b := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  rw [← hunion, Finset.sum_union hdisj]
