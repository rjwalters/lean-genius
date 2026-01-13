/-
  Erdős Problem #5: Prime Gap Limit Points

  Source: https://erdosproblems.com/5
  Status: OPEN

  Statement:
  Let p_n denote the nth prime. For any C ≥ 0, does there exist an infinite
  sequence n_i such that:
    lim_{i→∞} (p_{n_i+1} - p_{n_i}) / log(n_i) = C

  Equivalently: Is the set S of limit points of (p_{n+1} - p_n) / log(n)
  equal to [0, ∞]?

  Known Results:
  - ∞ ∈ S: Westzynthius proved arbitrarily large prime gaps exist
  - 0 ∈ S: Goldston-Pintz-Yildirim established results on small gaps
  - S has positive Lebesgue measure (Erdős, Ricci independently)
  - S contains arbitrarily large finite values (Hildebrand-Maier)
  - [0, c] ⊆ S for some small c > 0 (Pintz)
  - At least 1/3 of [0, ∞) belongs to S (Merikoski)
  - S has bounded gaps (Merikoski)

  What We Can Do:
  1. Define the prime gap function g(n) = p_{n+1} - p_n
  2. Define the normalized gap function g(n) / log(n)
  3. Define the set of limit points S
  4. State the conjecture formally
  5. Prove basic properties about prime gaps

  Tags: number-theory, primes, prime-gaps, erdos-problem
-/

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace Erdos5

open Filter Real Topology

/-! ## Part I: Basic Definitions -/

/-- The nth prime number (0-indexed: p_0 = 2, p_1 = 3, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap g(n) = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The normalized prime gap: g(n) / log(n).
    This is the quantity whose limit points we study. -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  if n = 0 then 0  -- Avoid log(0)
  else (primeGap n : ℝ) / Real.log n

/-! ## Part II: The Set of Limit Points -/

/-- A value C is a limit point of the normalized gap sequence if there exists
    a subsequence converging to C. -/
def IsLimitPoint (C : ℝ) : Prop :=
  ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (normalizedGap ∘ f) atTop (nhds C)

/-- The set S of all limit points. -/
def limitPointSet : Set ℝ := {C | IsLimitPoint C}

/-- Infinity is a limit point if normalized gaps are unbounded along some subsequence. -/
def InfinityIsLimitPoint : Prop :=
  ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (normalizedGap ∘ f) atTop atTop

/-! ## Part III: The Main Conjecture -/

/-- **Erdős Problem #5** (Main Conjecture)

    Every non-negative real number is a limit point of the normalized prime gaps.
    Together with ∞ being a limit point, this says S = [0, ∞]. -/
def erdos_5 : Prop :=
  (∀ C : ℝ, 0 ≤ C → IsLimitPoint C) ∧ InfinityIsLimitPoint

/-! ## Part IV: Known Results -/

/-- **Westzynthius (1931)**: Prime gaps can be arbitrarily large.
    Equivalently, ∞ is a limit point of normalized gaps.

    More precisely: lim sup (p_{n+1} - p_n) / log(p_n) = ∞ -/
axiom westzynthius_large_gaps : InfinityIsLimitPoint

/-- **Goldston-Pintz-Yildirim (2005)**: There are infinitely many prime gaps
    smaller than the average.

    This implies 0 is a limit point of normalized gaps. -/
axiom goldston_pintz_yildirim_small_gaps : IsLimitPoint 0

/-- **Erdős-Ricci**: The set S has positive Lebesgue measure. -/
axiom erdos_ricci_positive_measure : ∃ ε : ℝ, ε > 0 ∧
  -- Informal: μ(S) > ε where μ is Lebesgue measure
  True

/-- **Merikoski (2020s)**: At least 1/3 of [0, ∞) belongs to S.
    Also: S has bounded gaps (no "large holes"). -/
axiom merikoski_density : ∃ density : ℝ, density ≥ 1/3 ∧
  -- Informal: μ(S ∩ [0, M]) / M ≥ density as M → ∞
  True

/-! ## Part V: Basic Properties -/

/-- The first few primes. -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  unfold nthPrime
  exact Nat.nth_prime_zero_eq_two

theorem nthPrime_one : nthPrime 1 = 3 := by
  unfold nthPrime
  exact Nat.nth_prime_one_eq_three

theorem nthPrime_two : nthPrime 2 = 5 := by
  unfold nthPrime
  exact Nat.nth_prime_two_eq_five

/-- Prime gaps are always positive (there's always a next prime). -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap nthPrime
  -- p_{n+1} > p_n since primes are strictly increasing
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) := by
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  omega

/-- The first prime gap: p_1 - p_0 = 3 - 2 = 1. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- The second prime gap: p_2 - p_1 = 5 - 3 = 2. -/
theorem primeGap_one : primeGap 1 = 2 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- The nth prime is prime. -/
lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) := by
  unfold nthPrime
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The nth prime is at least 2. -/
lemma nthPrime_ge_two (n : ℕ) : nthPrime n ≥ 2 :=
  (nthPrime_prime n).two_le

/-- Primes grow at least linearly. -/
theorem nthPrime_strictMono : StrictMono nthPrime := by
  intro a b hab
  unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/-- The nth prime is at least n + 2. -/
theorem nthPrime_ge (n : ℕ) : nthPrime n ≥ n + 2 := by
  induction n with
  | zero =>
    -- p_0 = 2 ≥ 0 + 2 = 2 ✓
    simp [nthPrime, Nat.nth_prime_zero_eq_two]
  | succ k ih =>
    -- ih: p_k ≥ k + 2
    -- Want: p_{k+1} ≥ k + 3
    -- We have: p_{k+1} > p_k (strict monotonicity)
    have hlt : nthPrime k < nthPrime (k + 1) := nthPrime_strictMono (Nat.lt_succ_self k)
    omega

/-! ## Part VI: Gap Distribution -/

/-- The average gap near n is approximately log(p_n) by the prime number theorem.
    We normalize by log(n) which is asymptotically equivalent. -/
noncomputable def averageGap (n : ℕ) : ℝ := Real.log (nthPrime n)

/-- Cramér's conjecture (1936): The largest gap near n is O((log p_n)²).
    This is stronger than what's needed for Erdős #5 but provides context. -/
def cramer_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (primeGap n : ℝ) ≤ C * (Real.log (nthPrime n))^2

/-! ## Part VII: Connections -/

/-- Extract a strictly increasing subsequence from a frequently-true predicate. -/
lemma strictly_increasing_from_frequently {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ i, P (f i) := by
  have hfreq : ∀ N, ∃ n ≥ N, P n := by
    intro N
    by_contra hc
    push_neg at hc
    apply h
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact hc n hn
  have hfreq' : ∀ N, ∃ n > N, P n := by
    intro N
    obtain ⟨n, hn, hPn⟩ := hfreq (N + 1)
    exact ⟨n, by omega, hPn⟩
  choose g hg_gt hg_P using hfreq'
  let f : ℕ → ℕ := fun n => Nat.rec (g 0) (fun k fk => g fk) n
  use f
  constructor
  · intro a b hab
    induction hab with
    | refl => exact hg_gt (f a)
    | step _ ih => exact Nat.lt_trans ih (hg_gt (f _))
  · intro i
    induction i with
    | zero => exact hg_P 0
    | succ k _ => exact hg_P (f k)

/-- The twin prime conjecture would imply 0 is a limit point (with specific
    subsequence of twin prime locations). -/
theorem twin_prime_implies_zero_limit (h : ∃ᶠ n in atTop, primeGap n = 2) :
    IsLimitPoint 0 := by
  -- Extract strictly increasing subsequence where primeGap = 2
  obtain ⟨f, hf_mono, hf_gap⟩ := strictly_increasing_from_frequently h
  use f, hf_mono
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Along the subsequence, normalizedGap (f k) = 2 / log (f k)
  -- This tends to 0 since log (f k) → ∞
  have h_f_tends : Tendsto f atTop atTop := StrictMono.tendsto_atTop hf_mono
  have h_log_tends : Tendsto (fun k => Real.log (f k : ℝ)) atTop atTop := by
    apply Tendsto.comp Real.tendsto_log_atTop
    exact Tendsto.comp tendsto_natCast_atTop_atTop h_f_tends
  -- Eventually log (f k) > 2 / ε
  have h_log_bound : ∀ᶠ k in atTop, Real.log (f k : ℝ) > 2 / ε := by
    rw [Filter.tendsto_atTop_atTop] at h_log_tends
    obtain ⟨N, hN⟩ := h_log_tends (2 / ε + 1)
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    linarith [hN k hk]
  -- Eventually f k > 1 (so log is positive)
  have h_f_pos : ∀ᶠ k in atTop, 1 < f k := by
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hf01 : f 0 < f 1 := hf_mono (Nat.zero_lt_one)
    have hf1k : f 1 < f k := hf_mono (by omega : 1 < k)
    omega
  -- Combine conditions
  obtain ⟨N, hN⟩ := (h_log_bound.and h_f_pos).exists_forall_of_atTop
  use N
  intro k hk
  obtain ⟨h_log_k, h_fk_gt1⟩ := hN k hk
  simp only [Function.comp_apply, dist_zero_right]
  -- Compute normalizedGap
  unfold normalizedGap
  have h_fk_ne : f k ≠ 0 := by omega
  simp only [h_fk_ne, ↓reduceIte]
  -- The gap is exactly 2
  have h_gap_eq : primeGap (f k) = 2 := hf_gap k
  rw [h_gap_eq]
  -- Compute: |2 / log (f k)| < ε
  have h_log_pos : 0 < Real.log (f k : ℝ) := by
    apply Real.log_pos
    exact_mod_cast h_fk_gt1
  have h_nonneg : 0 ≤ ((2 : ℕ) : ℝ) / Real.log (f k : ℝ) := by
    apply div_nonneg
    · norm_num
    · exact le_of_lt h_log_pos
  rw [Real.norm_of_nonneg h_nonneg]
  -- 2 / log (f k) < ε since log (f k) > 2 / ε
  rw [div_lt_iff₀ h_log_pos]
  -- Normalize the ↑2 to 2
  simp only [Nat.cast_ofNat]
  have h1 : ε * Real.log (f k : ℝ) > ε * (2 / ε) := by
    apply mul_lt_mul_of_pos_left h_log_k hε
  have h2 : ε * (2 / ε) = 2 := by field_simp
  linarith

/-- Zhang's theorem (2013): There are infinitely many gaps ≤ 70,000,000.
    This was later improved to gaps ≤ 246 by the Polymath project. -/
axiom zhang_bounded_gaps : ∃ H : ℕ, ∃ᶠ n in atTop, primeGap n ≤ H

/-- Zhang's theorem implies 0 is a limit point. -/
theorem zhang_implies_zero_limit : IsLimitPoint 0 := by
  obtain ⟨H, hfreq⟩ := zhang_bounded_gaps
  obtain ⟨f, hf_mono, hf_gap⟩ := strictly_increasing_from_frequently hfreq
  use f, hf_mono
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_f_tends : Tendsto f atTop atTop := StrictMono.tendsto_atTop hf_mono
  have h_log_tends : Tendsto (fun k => Real.log (f k : ℝ)) atTop atTop := by
    apply Tendsto.comp Real.tendsto_log_atTop
    exact Tendsto.comp tendsto_natCast_atTop_atTop h_f_tends
  -- Eventually log (f k) > H / ε
  have h_log_bound : ∀ᶠ k in atTop, Real.log (f k : ℝ) > H / ε := by
    rw [Filter.tendsto_atTop_atTop] at h_log_tends
    obtain ⟨N, hN⟩ := h_log_tends (H / ε + 1)
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have := hN k hk
    linarith
  -- Eventually f k > 1
  have h_f_pos : ∀ᶠ k in atTop, 1 < f k := by
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have hf01 : f 0 < f 1 := hf_mono (Nat.zero_lt_one)
    have hf1k : f 1 < f k := hf_mono (by omega : 1 < k)
    have hf1_ge1 : f 1 ≥ 1 := by omega
    omega
  -- Combine the eventually conditions
  obtain ⟨N, hN⟩ := (h_log_bound.and h_f_pos).exists_forall_of_atTop
  use N
  intro k hk
  obtain ⟨h_log_k, h_fk_gt1⟩ := hN k hk
  simp only [Function.comp_apply, dist_zero_right]
  have h_fk_pos : 0 < (f k : ℝ) := by
    have : 1 < f k := h_fk_gt1
    have : 0 < f k := by omega
    exact Nat.cast_pos.mpr this
  have h_log_pos : 0 < Real.log (f k : ℝ) := by
    apply Real.log_pos
    have : 1 < f k := h_fk_gt1
    exact_mod_cast this
  unfold normalizedGap
  have h_fk_ne : f k ≠ 0 := by
    have : 1 < f k := h_fk_gt1
    omega
  simp only [h_fk_ne, ↓reduceIte]
  have h_gap : primeGap (f k) ≤ H := hf_gap k
  have h_bound : (primeGap (f k) : ℝ) / Real.log (f k : ℝ) ≤ H / Real.log (f k : ℝ) := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast h_gap
    · exact le_of_lt h_log_pos
  -- Key: log (f k) > H / ε implies H / log (f k) < ε
  have h_final : (H : ℝ) / Real.log (f k : ℝ) < ε := by
    have hlog : Real.log (f k : ℝ) > H / ε := h_log_k
    have hε_pos : (0 : ℝ) < ε := hε
    have h_log_pos' : Real.log (f k : ℝ) > 0 := h_log_pos
    have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
    rw [div_lt_iff₀ h_log_pos']
    have h1 : ε * Real.log (f k : ℝ) > ε * (H / ε) := by
      apply mul_lt_mul_of_pos_left hlog hε_pos
    have h2 : ε * ((H : ℝ) / ε) = H := by field_simp
    linarith
  have h_nonneg : 0 ≤ (primeGap (f k) : ℝ) / Real.log (f k : ℝ) := by
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact le_of_lt h_log_pos
  rw [Real.norm_of_nonneg h_nonneg]
  linarith

#check erdos_5
#check limitPointSet
#check IsLimitPoint

end Erdos5
