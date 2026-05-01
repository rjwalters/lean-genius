/- Erdős Problem #404: Prime Power Divisibility of Factorial Sums

Source: https://erdosproblems.com/404
Status: OPEN

Statement:
For which integers a ≥ 1 and primes p is there a finite upper bound on those k
such that there exist a = a₁ < a₂ < ··· < aₙ with p^k | (a₁! + a₂! + ··· + aₙ!)?

Let f(a, p) denote the greatest such k if it exists. How does f(a, p) behave?

Known results:
- Lin (1976): f(2, 2) ≤ 254

Axioms: 1 (lin_bound_meaning — Lin 1976 result; lin_bound is now derived)
Sorries: 0

Tags: number-theory, p-adic-valuation, factorials, divisibility, open-problem
-/

import Mathlib

open Nat Finset Filter

namespace Erdos404

/- ## Part I: Core Definitions -/

structure StrictIncSeq (a : ℕ) where
  length : ℕ
  seq : Fin length → ℕ
  starts_at_a : length > 0 → seq ⟨0, by omega⟩ = a
  strictly_increasing : ∀ i j : Fin length, i < j → seq i < seq j

noncomputable def factorialSum (s : StrictIncSeq a) : ℕ :=
  ∑ i : Fin s.length, (s.seq i).factorial

def dividesByPrimePower (a k : ℕ) (p : ℕ) : Prop :=
  ∃ s : StrictIncSeq a, p^k ∣ factorialSum s

def divisiblePowers (a : ℕ) (p : ℕ) : Set ℕ :=
  {k | dividesByPrimePower a k p}

noncomputable def f (a : ℕ) (p : ℕ) : ℕ :=
  sSup (divisiblePowers a p)

/- ## Part II: Main Questions -/

def secondaryQuestion : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ seq : ℕ → ℕ, StrictMono seq ∧
    Tendsto (fun k => padicValNat p (∑ i ∈ Finset.range (k+1), (seq i).factorial)) atTop atTop

def erdos404Conjecture : Prop :=
  ∀ a : ℕ, a ≥ 1 → ∀ p : ℕ, p.Prime → ∃ B : ℕ, f a p ≤ B

/- ## Part III: Known Results -/

/-- Lin (1976) [Bell Labs internal memorandum]: no strictly increasing sequence
    starting at 2 has 2^255 dividing its factorial sum.
    This is the fundamental statement of Lin's bound. -/
axiom lin_bound_meaning : ∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s)

/-- Lin (1976) bound `f 2 2 ≤ 254`, derived from `lin_bound_meaning`.

    Proof: If `k ∈ divisiblePowers 2 2`, then some sequence `s` has `2^k ∣ factorialSum s`.
    If `k ≥ 255`, then `2^255 ∣ 2^k ∣ factorialSum s`, contradicting `lin_bound_meaning`.
    Hence the set is bounded above by 254, so its supremum is ≤ 254 by `Nat.sSup_def`. -/
theorem lin_bound : f 2 2 ≤ 254 := by
  show sSup (divisiblePowers 2 2) ≤ 254
  have hbdd : ∀ k ∈ divisiblePowers 2 2, k ≤ 254 := by
    intro k hk
    obtain ⟨s, hs⟩ := hk
    by_contra h_gt
    push_neg at h_gt
    exact lin_bound_meaning s
      (dvd_trans (pow_dvd_pow 2 (by omega : 255 ≤ k)) hs)
  rw [Nat.sSup_def ⟨254, hbdd⟩]
  exact Nat.find_min' _ hbdd

/- ## Part IV: p-adic Analysis -/

noncomputable def legendreSum (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log p n + 1), n / p ^ (i + 1)

/-- Legendre's formula: ν_p(n!) = ∑_{i=1}^{⌊log_p n⌋+1} ⌊n/p^i⌋.
    Proved from Mathlib's padicValNat_factorial by reindexing. -/
theorem legendre_formula (n p : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    padicValNat p n.factorial = legendreSum n p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (show Nat.log p n < Nat.log p n + 2 by omega),
      Finset.sum_Ico_eq_sum_range]
  unfold legendreSum
  have h1 : Nat.log p n + 2 - 1 = Nat.log p n + 1 := by omega
  rw [h1]
  exact Finset.sum_congr rfl fun k _ => by rw [add_comm]

/- ## Part IV-A: The digit-sum identity and bounds

Key identity: legendreSum(n,p) * (p-1) + baseDigitSum(n,p) = n
where baseDigitSum is the sum of base-p digits.

This is proved by telescoping: each step uses the division algorithm
  a = (a/p)*p + a%p
to show
  (a/p)*(p-1) + a%p = a - a/p
and the sum telescopes to n - n/p^(L+1) = n. -/

/-- Sum of base-p digits of n (via iterated division). -/
def baseDigitSum (n p : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (Nat.log p n + 1), n / p ^ k % p

/-- n / p^k is weakly decreasing in k for p ≥ 1. -/
private theorem div_pow_antitone (n p : ℕ) (hp : 1 ≤ p) :
    ∀ k, n / p ^ (k + 1) ≤ n / p ^ k :=
  fun k => Nat.div_le_div_left (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)) (by positivity)

/-- Telescoping sum in ℕ for weakly decreasing f. -/
private theorem sum_telescope_nat (f : ℕ → ℕ) (hf : ∀ k, f (k + 1) ≤ f k) (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), (f k - f (k + 1)) = f 0 - f (L + 1) := by
  induction L with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : f (m + 2) ≤ f (m + 1) := hf (m + 1)
    have h2 : f (m + 1) ≤ f 0 := by
      clear ih h1; induction m with
      | zero => exact hf 0
      | succ k ihk => exact le_trans (hf (k + 1)) ihk
    omega

/-- Key identity: legendreSum * (p-1) + baseDigitSum = n.
    Proof by telescoping the division algorithm identity. -/
theorem legendreSum_digitSum_identity (n p : ℕ) (hp : 2 ≤ p) :
    legendreSum n p * (p - 1) + baseDigitSum n p = n := by
  unfold legendreSum baseDigitSum
  set L := Nat.log p n
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  -- Each term: n/p^(k+1)*(p-1) + n/p^k%p = n/p^k - n/p^(k+1)
  have h_eq : ∀ k ∈ range (L + 1),
      n / p ^ (k + 1) * (p - 1) + n / p ^ k % p = n / p ^ k - n / p ^ (k + 1) := by
    intro k _
    -- From division algorithm: a = (a/p)*p + a%p where a = n/p^k
    have h_div_alg := Nat.div_add_mod (n / p ^ k) p
    -- n/p^k/p = n/p^(k+1)
    have h_eq_div : n / p ^ k / p = n / p ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      exact (pow_succ p k).symm
    -- Monotonicity: n/p^k ≥ n/p^(k+1)
    have h_mono : n / p ^ (k + 1) ≤ n / p ^ k := div_pow_antitone n p (by omega) k
    -- From h_div_alg: p * (n/p^k/p) + n/p^k%p = n/p^k
    -- Rewrite n/p^k/p = n/p^(k+1):
    -- p * (n/p^(k+1)) + n/p^k%p = n/p^k
    -- So: n/p^(k+1)*(p-1) + n/p^k%p + n/p^(k+1) = n/p^k
    -- Therefore: n/p^(k+1)*(p-1) + n/p^k%p = n/p^k - n/p^(k+1)
    rw [← h_eq_div] at h_div_alg
    omega
  rw [Finset.sum_congr rfl h_eq,
      sum_telescope_nat (fun k => n / p ^ k) (div_pow_antitone n p (by omega)) L]
  simp only [pow_zero, Nat.div_one]
  -- n - n/p^(L+1) = n because p^(L+1) > n
  have h_zero : n / p ^ (L + 1) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by omega : 1 < p) n)
  omega

/-- Upper bound: ν_p(n!) * (p-1) ≤ n. -/
theorem padic_val_factorial_upper (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    padicValNat p n.factorial * (p - 1) ≤ n := by
  rw [legendre_formula n p hp (by omega)]
  have := legendreSum_digitSum_identity n p hp.two_le
  omega

/-- Lower bound: n - (p-1)(⌊log_p n⌋ + 1) ≤ ν_p(n!) * (p-1). -/
theorem padic_val_factorial_lower (n p : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    n - (p - 1) * (Nat.log p n + 1) ≤ padicValNat p n.factorial * (p - 1) := by
  rw [legendre_formula n p hp (by omega)]
  have h_id := legendreSum_digitSum_identity n p hp.two_le
  -- baseDigitSum ≤ (p-1)*(L+1) since each digit < p
  have h_ds : baseDigitSum n p ≤ (p - 1) * (Nat.log p n + 1) := by
    unfold baseDigitSum
    calc ∑ k ∈ Finset.range (Nat.log p n + 1), n / p ^ k % p
        ≤ ∑ _ ∈ Finset.range (Nat.log p n + 1), (p - 1) := by
          apply Finset.sum_le_sum; intro k _
          have := Nat.mod_lt (n / p ^ k) (show 0 < p by omega); omega
      _ = (p - 1) * (Nat.log p n + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

/-- ν_p(n!)/n → 1/(p-1) as n → ∞.
    Proof by squeeze theorem using the Nat-valued bounds. -/
theorem padic_val_factorial_asymp (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n => (padicValNat p n.factorial : ℝ) / n) atTop (nhds (1/(p-1))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_one_lt : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  -- Upper bound: ν/n ≤ 1/(p-1)
  have h_upper : ∀ᶠ n in atTop, (padicValNat p n.factorial : ℝ) / n ≤ 1 / ((p : ℝ) - 1) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [div_le_div_iff hn_pos hpp1, one_mul]
    exact_mod_cast padic_val_factorial_upper n p hp (by omega)
  -- Lower bound limit: 1/(p-1) - (L+1)/n → 1/(p-1)
  have h_lower_lim : Tendsto (fun n : ℕ =>
      1 / ((p : ℝ) - 1) - ((Nat.log p n : ℝ) + 1) / n) atTop (nhds (1 / ((p : ℝ) - 1))) := by
    have : Tendsto (fun n : ℕ => ((Nat.log p n : ℝ) + 1) / n) atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hlogp : (0 : ℝ) < Real.log ↑p := Real.log_pos (by exact_mod_cast hp.one_lt)
      -- From little-o: eventually |log x| ≤ (ε·log p / 2)·|x|
      obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
        ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
          (show (0 : ℝ) < ε * Real.log ↑p / 2 by positivity))
      refine ⟨max ⌈R⌉₊ (⌈2 / ε⌉₊ + 1), fun n hn => ?_⟩
      have hn1 : 1 ≤ n := by have := le_trans (le_max_right _ _) hn; omega
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
      rw [Real.dist_eq, sub_zero,
          abs_of_nonneg (div_nonneg (by positivity) hn_pos.le)]
      -- Step 1: Nat.log p n · log p ≤ log n (from p^(log_p n) ≤ n)
      have h1 : (Nat.log p n : ℝ) * Real.log ↑p ≤ Real.log ↑n := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity)
          (by exact_mod_cast Nat.pow_log_le_self p (show n ≠ 0 by omega))
      -- Step 2: log n ≤ (ε·log p / 2)·n (from isLittleO bound)
      have h2 : Real.log ↑n ≤ ε * Real.log ↑p / 2 * ↑n := by
        have h := hR ↑n (le_trans (Nat.le_ceil R)
          (by exact_mod_cast le_trans (le_max_left _ _) hn))
        simp only [rpow_one, Real.norm_eq_abs] at h
        rwa [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn1)),
             abs_of_nonneg hn_pos.le] at h
      -- Step 3: Nat.log p n / n ≤ ε/2 (dividing combined bound by log p)
      have h3 : (Nat.log p n : ℝ) / ↑n ≤ ε / 2 := by
        rw [div_le_iff hn_pos]
        exact (mul_le_mul_right hlogp).mp
          ((le_trans h1 h2).trans_eq (by ring))
      -- Step 4: 1/n < ε/2 (since n > 2/ε)
      have h4 : 1 / (↑n : ℝ) < ε / 2 := by
        rw [div_lt_div_iff hn_pos (by norm_num : (0 : ℝ) < 2), one_mul]
        have : (⌈2 / ε⌉₊ : ℝ) + 1 ≤ ↑n := by
          exact_mod_cast le_trans (le_max_right _ _) hn
        nlinarith [Nat.le_ceil (2 / ε)]
      -- Combine
      calc ((Nat.log p n : ℝ) + 1) / ↑n
          = (Nat.log p n : ℝ) / ↑n + 1 / ↑n := add_div ..
        _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt h3 h4
        _ = ε := by ring
    rw [show (1 : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) - 0 from by ring]
    exact Tendsto.sub tendsto_const_nhds this
  -- Lower bound pointwise: ν/n ≥ 1/(p-1) - (L+1)/n
  have h_lower : ∀ᶠ n in atTop, 1 / ((p : ℝ) - 1) - ((Nat.log p n : ℝ) + 1) / n ≤
      (padicValNat p n.factorial : ℝ) / n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    -- Use additive identity: ν*(p-1) + ds = n, ds ≤ (p-1)*(L+1)
    have h_id := legendreSum_digitSum_identity n p hp.two_le
    have h_ds : baseDigitSum n p ≤ (p - 1) * (Nat.log p n + 1) := by
      unfold baseDigitSum
      calc ∑ k ∈ Finset.range (Nat.log p n + 1), n / p ^ k % p
          ≤ ∑ _ ∈ Finset.range (Nat.log p n + 1), (p - 1) := by
            apply Finset.sum_le_sum; intro k _
            have := Nat.mod_lt (n / p ^ k) (show 0 < p by omega); omega
        _ = (p - 1) * (Nat.log p n + 1) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [legendre_formula n p hp (by omega)]
    -- Goal: 1/(p-1) - (L+1)/n ≤ (legendreSum n p : ℝ) / n
    -- From h_id: (legendreSum : ℝ) * (p-1) = n - (baseDigitSum : ℝ)
    -- So (legendreSum : ℝ) = (n - ds) / (p-1)
    -- And (legendreSum : ℝ) / n = 1/(p-1) - ds/(n*(p-1))
    -- Since ds ≤ (p-1)*(L+1): ds/(n*(p-1)) ≤ (L+1)/n
    -- Therefore legendreSum/n ≥ 1/(p-1) - (L+1)/n
    have h_id_real : (legendreSum n p : ℝ) * ((p : ℝ) - 1) + (baseDigitSum n p : ℝ) = (n : ℝ) := by
      have h1 : (legendreSum n p * (p - 1) + baseDigitSum n p : ℕ) = n := h_id
      push_cast [Nat.cast_sub hp.one_lt.le] at h1
      linarith
    have h_ds_real : (baseDigitSum n p : ℝ) ≤ ((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1) := by
      push_cast [Nat.cast_sub hp.one_lt.le] at h_ds
      linarith
    -- Now do the algebra
    have h_leg : (legendreSum n p : ℝ) * ((p : ℝ) - 1) ≥
        (n : ℝ) - ((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1) := by linarith
    rw [ge_iff_le, ← sub_nonneg]
    rw [ge_iff_le, ← sub_nonneg] at h_leg
    rw [sub_div]
    have : (legendreSum n p : ℝ) / (n : ℝ) - (1 / ((p : ℝ) - 1) - ((Nat.log p n : ℝ) + 1) / (n : ℝ)) =
        ((legendreSum n p : ℝ) * ((p : ℝ) - 1) - ((n : ℝ) - ((p : ℝ) - 1) * ((Nat.log p n : ℝ) + 1))) /
        ((n : ℝ) * ((p : ℝ) - 1)) := by field_simp
    linarith [div_nonneg h_leg (mul_pos hn_pos hpp1).le]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_lower_lim tendsto_const_nhds h_lower h_upper

/- ## Part V: Structure of Factorial Sums -/

/-- For a₁ ≤ a₂, a₁! + a₂! = a₁! * (1 + a₂!/a₁!) since a₁! | a₂!. -/
theorem factorial_sum_factored (a₁ a₂ : ℕ) (h : a₁ ≤ a₂) :
    a₁.factorial + a₂.factorial = a₁.factorial * (1 + a₂.factorial / a₁.factorial) := by
  have hdvd : a₁.factorial ∣ a₂.factorial := Nat.factorial_dvd_factorial h
  rw [mul_add, mul_one, Nat.mul_div_cancel' hdvd]

/- ## Part VI: Examples -/

example : 2^3 ∣ Nat.factorial 2 + Nat.factorial 3 := by native_decide
example : 3 ∣ Nat.factorial 1 + Nat.factorial 2 := by native_decide
example : 3^2 ∣ Nat.factorial 1 + Nat.factorial 2 + Nat.factorial 3 := by native_decide

/- ## Part VII: Summary -/

theorem erdos_404_summary :
    f 2 2 ≤ 254 ∧
    (∀ s : StrictIncSeq 2, ¬(2^255 ∣ factorialSum s)) := by
  exact ⟨lin_bound, lin_bound_meaning⟩

end Erdos404
