/-
# Erdős Problem #234: Density of Normalized Prime Gaps

For every c ≥ 0, the density f(c) of integers n for which
(p_{n+1} - p_n) / log n < c exists and is a continuous function of c.

## Status: OPEN

## References
- Cramér, "On the order of magnitude of prime gaps" (1936)
- Gallagher, "On the distribution of primes in short intervals" (1976)
- Erdős, "On the difference of consecutive primes" (1935, 1940)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import Proofs.RiemannHypothesis

open Nat Filter Real Set

/-
## Section I: Basic Definitions
-/

/-- The n-th prime number (0-indexed via Nat.nth). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime gap: g_n = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Normalized prime gap: g_n / log n. For n ≤ 1 we define this as 0. -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  if n ≤ 1 then 0 else (primeGap n : ℝ) / Real.log n

/-
## Section II: Counting Functions
-/

/-- Count of integers n < N for which the normalized gap is less than c. -/
noncomputable def countSmallNormGaps (N : ℕ) (c : ℝ) : ℕ :=
  ((Finset.range N).filter (fun n => normalizedGap n < c)).card

/-- Proportion of integers n < N with normalized gap < c. -/
noncomputable def gapProportion (N : ℕ) (c : ℝ) : ℝ :=
  (countSmallNormGaps N c : ℝ) / N

/-
## Section III: The Conjecture
-/

/-- The density f(c) exists for a given c when the limit exists. -/
def DensityExists (c : ℝ) : Prop :=
  ∃ f : ℝ, Tendsto (fun N => gapProportion N c) atTop (nhds f)

/-- **Erdős Problem #234**: For every c ≥ 0, the density f(c) of integers n
with (p_{n+1} - p_n)/log n < c exists and is a continuous function of c.

This has two parts:
1. The limit defining f(c) exists for all c ≥ 0.
2. The resulting function f : [0, ∞) → [0, 1] is continuous.
-/
def ErdosProblem234 : Prop :=
  (∀ c ≥ 0, DensityExists c) ∧
  ∃ f : ℝ → ℝ, Continuous f ∧
    ∀ c ≥ 0, Tendsto (fun N => gapProportion N c) atTop (nhds (f c))

/-
## Section IV: Basic Properties
-/

/-- Normalized gap is non-negative. -/
lemma normalizedGap_nonneg (n : ℕ) : normalizedGap n ≥ 0 := by
  unfold normalizedGap
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg (primeGap n)
    · push_neg at h
      exact Real.log_nonneg (Nat.one_lt_cast.mpr h).le

/-- No integers have normalized gap < 0. -/
lemma countSmallNormGaps_zero (N : ℕ) : countSmallNormGaps N 0 = 0 := by
  unfold countSmallNormGaps
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  simp only [not_lt]
  exact normalizedGap_nonneg n

/-- Gap proportion at c = 0 is always 0. -/
lemma gapProportion_zero (N : ℕ) : gapProportion N 0 = 0 := by
  unfold gapProportion
  rw [countSmallNormGaps_zero]
  simp

/-- f(0) = 0: the density at zero is zero. -/
theorem density_at_zero (h : DensityExists 0) :
    ∃ f, Tendsto (fun N => gapProportion N 0) atTop (nhds f) ∧ f = 0 := by
  use 0
  constructor
  · simp only [gapProportion_zero]
    exact tendsto_const_nhds
  · rfl

/-- Gap proportion is non-negative. -/
lemma gapProportion_nonneg (N : ℕ) (c : ℝ) : gapProportion N c ≥ 0 := by
  unfold gapProportion
  apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Gap proportion is at most 1. -/
lemma gapProportion_le_one (N : ℕ) (c : ℝ) (hN : 0 < N) : gapProportion N c ≤ 1 := by
  unfold gapProportion
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact Nat.cast_le.mpr (Finset.card_filter_le _ _)

/-- The count of small normalized gaps is monotone in the threshold c. -/
lemma countSmallNormGaps_mono (N : ℕ) (c₁ c₂ : ℝ) (hc : c₁ ≤ c₂) :
    countSmallNormGaps N c₁ ≤ countSmallNormGaps N c₂ := by
  unfold countSmallNormGaps
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro n hn
  exact lt_of_lt_of_le hn hc

/-- f(c) is non-decreasing: more integers satisfy a larger threshold. -/
theorem density_monotone (c₁ c₂ : ℝ) (hc : c₁ ≤ c₂) :
    ∀ N, gapProportion N c₁ ≤ gapProportion N c₂ := by
  intro N
  unfold gapProportion
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact Nat.cast_le.mpr (countSmallNormGaps_mono N c₁ c₂ hc)

/-
## Section IV': Proving density_at_infinity via Markov's Inequality

The following derives density_at_infinity from average_normalized_gap,
reducing the axiom count from 5 to 4. The argument:

1. Markov bound: for non-negative normalizedGap and c > 0,
   #{n < N : gap(n) ≥ c} ≤ (∑ gap(n)) / c
2. Therefore gapProportion N c ≥ 1 - (average gap) / c
3. Since average gap → 1 (by PNT, axiom average_normalized_gap),
   for any ε > 0, eventually gapProportion N c > 1 - ε when c is large enough.
-/

/-- Finite Markov bound for normalizedGap: the number of indices where the
gap is at least c times the sum divided by c. -/
private lemma finset_markov_bound (N : ℕ) (c : ℝ) (hc : c > 0) :
    c * ↑((Finset.range N).filter (fun n => ¬(normalizedGap n < c))).card
    ≤ ∑ n ∈ Finset.range N, normalizedGap n := by
  calc c * ↑((Finset.range N).filter (fun n => ¬(normalizedGap n < c))).card
      = ∑ _n ∈ (Finset.range N).filter (fun n => ¬(normalizedGap n < c)), c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ (Finset.range N).filter (fun n => ¬(normalizedGap n < c)), normalizedGap n := by
        apply Finset.sum_le_sum
        intro n hn
        exact le_of_not_lt (Finset.mem_filter.mp hn).2
    _ ≤ ∑ n ∈ Finset.range N, normalizedGap n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact normalizedGap_nonneg i

/-- Complement card: #{n < N : gap ≥ c} = N - countSmallNormGaps N c. -/
private lemma complement_card (N : ℕ) (c : ℝ) :
    ((Finset.range N).filter (fun n => ¬(normalizedGap n < c))).card
    = N - countSmallNormGaps N c := by
  unfold countSmallNormGaps
  have := Finset.filter_card_add_filter_neg_card_eq_card
    (Finset.range N) (fun n => normalizedGap n < c)
  rw [Finset.card_range] at this
  omega

/-- Markov bound on gap proportion: gapProportion N c ≥ 1 - (avg gap)/c. -/
private lemma gapProportion_markov (N : ℕ) (hN : 0 < N) (c : ℝ) (hc : c > 0) :
    gapProportion N c ≥
    1 - (∑ n ∈ Finset.range N, normalizedGap n) / (↑N * c) := by
  -- From finset_markov_bound: c * |B| ≤ ∑ gap
  -- From complement_card: |B| = N - count
  -- So c * (N - count) ≤ ∑ gap, i.e. N*c - count*c ≤ ∑ gap
  -- Rearranging: count*c ≥ N*c - ∑ gap, count ≥ N - (∑ gap)/c
  -- Dividing by N: gapProportion ≥ 1 - (∑ gap)/(N*c)
  have hNr : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hNc : (0 : ℝ) < ↑N * c := mul_pos hNr hc
  have hmark := finset_markov_bound N c hc
  have hcomp := complement_card N c
  unfold gapProportion
  rw [ge_iff_le, ← sub_nonneg]
  -- Goal: 0 ≤ countSmallNormGaps N c / N - (1 - sum / (N * c))
  -- = countSmallNormGaps N c / N - 1 + sum / (N * c)
  -- = (countSmallNormGaps N c * c + sum - N * c) / (N * c)
  -- From hmark: c * (N - countSmallNormGaps N c) ≤ sum (in ℕ then ℝ)
  -- i.e. N*c - count*c ≤ sum, i.e. count*c + sum ≥ N*c
  -- So numerator ≥ 0.
  have h_count_le : countSmallNormGaps N c ≤ N := by
    unfold countSmallNormGaps
    exact Finset.card_filter_le _ _
  -- Cast to ℝ: ↑(N - count) = ↑N - ↑count since count ≤ N
  have h_sub_cast : (↑(N - countSmallNormGaps N c) : ℝ) = ↑N - ↑(countSmallNormGaps N c) := by
    exact Nat.cast_sub h_count_le
  -- From hmark with complement_card substituted:
  -- c * ↑(N - count) ≤ sum
  rw [hcomp] at hmark
  rw [h_sub_cast] at hmark
  -- hmark : c * (↑N - ↑count) ≤ sum
  -- Goal: 0 ≤ ↑count / ↑N - 1 + sum / (↑N * c)
  rw [div_add_div _ _ (ne_of_gt hNr) (ne_of_gt hNc)]
  rw [sub_nonneg, div_le_div_iff (by positivity) (mul_pos hNr hNc)]
  -- After simplification: 1 * (↑N * (↑N * c)) ≤ ↑count * (↑N * c) + sum * ↑N
  -- From hmark: c * ↑N - c * ↑count ≤ sum
  -- So sum * ↑N ≥ (c * ↑N - c * ↑count) * ↑N = c * ↑N² - c * ↑count * ↑N
  -- ↑count * (↑N * c) + sum * ↑N ≥ ↑count * ↑N * c + c * ↑N² - c * ↑count * ↑N = c * ↑N²
  -- = ↑N * (↑N * c) = 1 * (↑N * (↑N * c))
  nlinarith [mul_comm c (↑N - ↑(countSmallNormGaps N c))]

/-- **density_at_infinity** (previously an axiom, now derived):
f(c) → 1 as c → ∞ — eventually all normalized gaps are below c.
Proved from average_normalized_gap via Markov's inequality. -/
theorem density_at_infinity :
    ∀ ε > 0, ∃ c₀ : ℝ, ∀ c ≥ c₀, ∀ᶠ N in atTop, gapProportion N c > 1 - ε := by
  intro ε hε
  -- Choose c₀ = 2/ε + 1 so that (1 + ε/2)/c₀ < ε
  refine ⟨2 / ε + 1, fun c hc => ?_⟩
  have hc_pos : c > 0 := by positivity
  -- From average_normalized_gap: eventually (∑ gap) / N < 1 + ε/2
  have h_avg : ∀ᶠ N in atTop,
      (∑ n ∈ Finset.range N, normalizedGap n) / ↑N < 1 + ε / 2 := by
    have h1 : (1 : ℝ) < 1 + ε / 2 := by linarith
    exact average_normalized_gap.eventually (Iio_mem_nhds h1)
  -- Eventually N > 0
  have h_pos : ∀ᶠ N in atTop, (0 : ℕ) < N :=
    eventually_atTop.mpr ⟨1, fun n hn => by omega⟩
  -- Combine
  filter_upwards [h_avg, h_pos] with N hN_avg hN_pos
  -- By Markov: gapProportion N c ≥ 1 - (sum/N)/c
  have hmarkov := gapProportion_markov N hN_pos c hc_pos
  -- Since sum/N < 1 + ε/2, we have (sum/N)/c < (1 + ε/2)/c ≤ (1 + ε/2)/c₀
  -- And (1 + ε/2)/(2/ε + 1) = ε(1 + ε/2)/(2 + ε) ≤ ε/2 < ε
  -- So gapProportion N c > 1 - ε
  -- sum/(N*c) = (sum/N)/c < (1 + ε/2)/c since sum/N < 1 + ε/2
  have h_bound : (∑ n ∈ Finset.range N, normalizedGap n) / (↑N * c)
    < (1 + ε / 2) / c := by
    rw [← div_div]
    exact (div_lt_div_right hc_pos).mpr hN_avg
  -- (1 + ε/2)/c ≤ ε/2 since c ≥ 2/ε + 1
  have h_bound2 : (1 + ε / 2) / c ≤ ε / 2 := by
    rw [div_le_div_iff hc_pos (by positivity : (0 : ℝ) < 2)]
    -- Goal: (1 + ε/2) * 2 ≤ ε * c, i.e., 2 + ε ≤ ε * c
    have h_key : ε * (2 / ε + 1) = 2 + ε := by field_simp
    have h_prod : ε * (2 / ε + 1) ≤ ε * c := mul_le_mul_of_nonneg_left hc hε.le
    nlinarith
  linarith

/-
## Section V: Cramér's Model
-/

/-- Cramér's model (1936) predicts an exponential distribution for
normalized prime gaps: f(c) = 1 - e^{-c} for c ≥ 0. -/
noncomputable def cramerPrediction (c : ℝ) : ℝ :=
  if c < 0 then 0 else 1 - Real.exp (-c)

/-- The exponential part of Cramér's prediction is continuous. -/
lemma cramer_exp_continuous : Continuous (fun c : ℝ => 1 - Real.exp (-c)) :=
  continuous_const.sub (continuous_exp.comp continuous_neg)

/-- Cramér prediction is continuous (both pieces are continuous and agree at 0). -/
theorem cramer_continuous : Continuous cramerPrediction := by
  unfold cramerPrediction
  apply Continuous.if_lt continuous_id continuous_const
  · exact continuous_const
  · exact continuous_const.sub (continuous_exp.comp continuous_neg)
  · intro x hx
    simp at hx
    rw [hx]
    simp

/-- Cramér prediction is a valid CDF: values lie in [0, 1] for c ≥ 0. -/
theorem cramer_in_unit_interval (c : ℝ) (hc : c ≥ 0) :
    0 ≤ cramerPrediction c ∧ cramerPrediction c ≤ 1 := by
  unfold cramerPrediction
  rw [if_neg (not_lt.mpr hc)]
  constructor
  · linarith [exp_le_one_of_nonpos (neg_nonpos.mpr hc)]
  · linarith [exp_pos (-c)]

/-
## Section VI: Gallagher's Conditional Result
-/

/-- Gallagher's theorem (1976): assuming the Riemann Hypothesis,
normalized prime gaps have exponential distribution in the limit.
Specifically, #{n ≤ x : g_n/log p_n ∈ [λ, λ+Δλ]}/π(x) → Δλ·e^{-λ}. -/
axiom gallagher_conditional :
    RiemannHypothesis →
    ∀ c ≥ 0, Tendsto (fun N => gapProportion N c) atTop (nhds (cramerPrediction c))

/-- Gallagher's result establishes the conjecture conditional on RH. -/
theorem gallagher_implies_conjecture (hRH : RiemannHypothesis) :
    ErdosProblem234 := by
  constructor
  · intro c hc
    use cramerPrediction c
    exact gallagher_conditional hRH c hc
  · use cramerPrediction
    constructor
    · exact cramer_continuous
    · intro c hc
      exact gallagher_conditional hRH c hc

/-
## Section VII: Partial Results on Gap Distribution
-/

/-- The average normalized gap tends to 1 by the Prime Number Theorem. -/
axiom average_normalized_gap :
    Tendsto (fun N => (∑ n ∈ Finset.range N, normalizedGap n) / N) atTop (nhds 1)

/-
## Section VII': Small gaps from average gap (axiom elimination)

Reduces axiom count from 4 to 3 by deriving small_gaps_exist from
average_normalized_gap. If only finitely many n had normalizedGap n < 1+ε,
the Cesàro average would exceed 1, contradicting average_normalized_gap.
-/

/-- The nth prime is at least n (primes form an infinite, strictly increasing subset of ℕ). -/
private lemma nthPrime_ge (n : ℕ) : n ≤ nthPrime n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have h_infinite : (setOf Nat.Prime).Infinite := by
      intro hf; obtain ⟨N, hN⟩ := hf.bddAbove
      obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (N + 1)
      have := hN hpp; omega
    have : nthPrime k < nthPrime (k + 1) :=
      Nat.nth_strictMono h_infinite (by omega : k < k + 1)
    omega

/-- If {n | normalizedGap n < c} were finite for c > 1, the Cesàro average
of normalizedGap would exceed 1, contradicting average_normalized_gap. -/
private lemma infinite_normalizedGap_lt (c : ℝ) (hc : c > 1) :
    {n : ℕ | normalizedGap n < c}.Infinite := by
  by_contra h_fin
  rw [Set.not_infinite] at h_fin
  obtain ⟨M, hM⟩ := h_fin.bddAbove
  -- For n > M: normalizedGap n ≥ c
  have h_ge : ∀ n : ℕ, M < n → normalizedGap n ≥ c := by
    intro n hn; by_contra hlt; push_neg at hlt
    exact absurd (hM hlt) (by omega)
  -- Sum lower bound: for N > M+1, ∑ normalizedGap ≥ (N-(M+1))·c
  have h_sum : ∀ N : ℕ, M + 1 < N →
      (∑ n ∈ Finset.range N, normalizedGap n) ≥ ↑(N - (M + 1)) * c := by
    intro N hN
    calc ∑ n ∈ Finset.range N, normalizedGap n
        ≥ ∑ n ∈ Finset.Ico (M + 1) N, normalizedGap n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr ((Finset.mem_Ico.mp hx).2))
            (fun i _ _ => normalizedGap_nonneg i)
      _ ≥ ∑ _n ∈ Finset.Ico (M + 1) N, c :=
          Finset.sum_le_sum fun n hn =>
            h_ge n (by have := (Finset.mem_Ico.mp hn).1; omega)
      _ = ↑(N - (M + 1)) * c := by
          rw [Finset.sum_const, Finset.card_Ico, nsmul_eq_mul]
  -- avg → 1 by average_normalized_gap, so eventually avg < (c+1)/2
  have h_mid : (1 : ℝ) < (c + 1) / 2 := by linarith
  have h_upper := average_normalized_gap.eventually (Iio_mem_nhds h_mid)
  -- Pick N satisfying: avg < (c+1)/2, N > M+1, and N large enough for sum bound
  have h_big : ∀ᶠ N in atTop, M + 1 < (N : ℕ) :=
    eventually_atTop.mpr ⟨M + 2, fun N hN => by omega⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * c * (↑M + 1) / (c - 1))
  have h_vbig : ∀ᶠ N in atTop, K ≤ (N : ℕ) :=
    eventually_atTop.mpr ⟨K, fun N hN => hN⟩
  obtain ⟨N, ⟨hN_avg, hNM⟩, hNK⟩ := ((h_upper.and h_big).and h_vbig).exists
  -- Derive contradiction: sum bound + avg bound + N size bound are incompatible
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (by omega)
  have hS := h_sum N hNM
  have h_avg_lt : (∑ n ∈ Finset.range N, normalizedGap n) < (c + 1) / 2 * ↑N :=
    (div_lt_iff hN_pos).mp hN_avg
  -- (N-(M+1))*c ≤ ∑ < (c+1)/2 * N, so (N-(M+1))*c < (c+1)/2 * N
  have hNM_cast : (↑(N - (M + 1)) : ℝ) = ↑N - ↑(M + 1) := Nat.cast_sub (by omega)
  rw [hNM_cast] at hS
  -- N*(c-1) > 2c*(M+1) from the Archimedean bound
  have hN_ge_K : (↑N : ℝ) ≥ ↑K := Nat.cast_le.mpr hNK
  have hN_real : (↑N : ℝ) > 2 * c * (↑M + 1) / (c - 1) := lt_of_lt_of_le hK hN_ge_K
  have hN_cleared : 2 * c * (↑M + 1) < ↑N * (c - 1) := by
    rwa [div_lt_iff (by linarith : (c : ℝ) - 1 > 0)] at hN_real
  -- (↑N - ↑(M+1))*c ≤ ∑ < (c+1)/2*↑N, but ↑N*(c-1) > 2c*(↑M+1) makes this impossible
  nlinarith

/-- For n ≥ 2 with normalizedGap n < c (c > 0), primeGap n < c · log(p_n),
since log(p_n) ≥ log(n) (the nth prime is at least n). -/
private lemma primeGap_lt_of_normalizedGap_lt (n : ℕ) (c : ℝ) (hn : n ≥ 2) (hc : c > 0)
    (h : normalizedGap n < c) :
    (primeGap n : ℝ) < c * Real.log (nthPrime n) := by
  have hlog_n_pos : Real.log (↑n) > 0 :=
    Real.log_pos (by exact_mod_cast show 1 < n by omega)
  have hlog_ge : Real.log (↑(nthPrime n)) ≥ Real.log (↑n) :=
    Real.log_le_log (by positivity) (Nat.cast_le.mpr (nthPrime_ge n))
  unfold normalizedGap at h
  simp only [show ¬(n ≤ 1) by omega, ↓reduceIte] at h
  rw [div_lt_iff hlog_n_pos] at h
  linarith [mul_le_mul_of_nonneg_left hlog_ge hc.le]

/-- **small_gaps_exist** (previously axiom, now theorem):
For any ε > 0, infinitely many n have g_n < (1+ε) · log(p_n).
Derived from average_normalized_gap via Cesàro contrapositive. -/
theorem small_gaps_exist (ε : ℝ) (hε : ε > 0) :
    {n : ℕ | (primeGap n : ℝ) < (1 + ε) * Real.log (nthPrime n)}.Infinite := by
  have h_inf := infinite_normalizedGap_lt (1 + ε) (by linarith)
  -- Remove n ≤ 1 from the infinite set (they may not satisfy the log bound)
  have h_inf2 : ({n : ℕ | normalizedGap n < 1 + ε} \ {n : ℕ | n < 2}).Infinite :=
    h_inf.diff (Set.toFinite _)
  apply h_inf2.mono
  intro n hn
  obtain ⟨hn_ng, hn_ge⟩ := Set.mem_diff.mp hn
  exact primeGap_lt_of_normalizedGap_lt n (1 + ε) (by omega) (by linarith) hn_ng

/-
## Section VIII: Additional Properties of Cramér's Model
-/

/-- Cramér prediction at 0 is 0. -/
theorem cramer_at_zero : cramerPrediction 0 = 0 := by
  unfold cramerPrediction
  simp

/-- Cramér prediction is non-negative for all c ≥ 0. -/
theorem cramer_nonneg (c : ℝ) (hc : c ≥ 0) : cramerPrediction c ≥ 0 :=
  (cramer_in_unit_interval c hc).1

/-- Cramér prediction is at most 1 for all c ≥ 0. -/
theorem cramer_le_one (c : ℝ) (hc : c ≥ 0) : cramerPrediction c ≤ 1 :=
  (cramer_in_unit_interval c hc).2

/-- Cramér prediction is monotone: if c₁ ≤ c₂ then f(c₁) ≤ f(c₂). -/
theorem cramer_monotone (c₁ c₂ : ℝ) (h1 : c₁ ≥ 0) (h2 : c₂ ≥ 0) (hle : c₁ ≤ c₂) :
    cramerPrediction c₁ ≤ cramerPrediction c₂ := by
  unfold cramerPrediction
  rw [if_neg (not_lt.mpr h1), if_neg (not_lt.mpr h2)]
  have : Real.exp (-c₂) ≤ Real.exp (-c₁) := by
    apply exp_le_exp.mpr
    linarith
  linarith

/-
## Section IX: Properties of the Density Function

If the density f(c) = lim_{N→∞} gapProportion(N, c) exists, these theorems
show it necessarily satisfies the properties of a cumulative distribution
function on [0, ∞): valued in [0, 1], monotone non-decreasing, and
approaching 1 as c → ∞. The limit behavior uses density_at_infinity
(proved from average_normalized_gap via Markov's inequality).
-/

/-- If the density exists at c, it is non-negative. -/
theorem density_function_nonneg (c : ℝ) (f : ℝ)
    (hf : Tendsto (fun N => gapProportion N c) atTop (nhds f)) : f ≥ 0 :=
  ge_of_tendsto hf (Eventually.of_forall fun N => gapProportion_nonneg N c)

/-- If the density exists at c, it is at most 1. -/
theorem density_function_le_one (c : ℝ) (f : ℝ)
    (hf : Tendsto (fun N => gapProportion N c) atTop (nhds f)) : f ≤ 1 :=
  le_of_tendsto hf (eventually_atTop.mpr ⟨1, fun N hN =>
    gapProportion_le_one N c (by omega)⟩)

/-- The density is monotone: if c₁ ≤ c₂ and both densities exist, f(c₁) ≤ f(c₂).
    Limit-level analogue of density_monotone. -/
theorem density_function_monotone (c₁ c₂ : ℝ) (hc : c₁ ≤ c₂) (f₁ f₂ : ℝ)
    (hf1 : Tendsto (fun N => gapProportion N c₁) atTop (nhds f₁))
    (hf2 : Tendsto (fun N => gapProportion N c₂) atTop (nhds f₂)) : f₁ ≤ f₂ := by
  have h_diff : Tendsto (fun N => gapProportion N c₂ - gapProportion N c₁)
      atTop (nhds (f₂ - f₁)) := hf2.sub hf1
  have h_nn : ∀ N, gapProportion N c₂ - gapProportion N c₁ ≥ 0 := fun N =>
    sub_nonneg.mpr (density_monotone c₁ c₂ hc N)
  linarith [ge_of_tendsto h_diff (Eventually.of_forall h_nn)]

/-- If the density exists for all c ≥ 0, then f(c) → 1 as c → ∞.
    Derived from density_at_infinity (which itself follows from
    average_normalized_gap via Markov's inequality). -/
theorem density_function_tendsto_one
    (f : ℝ → ℝ)
    (hf : ∀ c : ℝ, c ≥ 0 → Tendsto (fun N => gapProportion N c) atTop (nhds (f c))) :
    Tendsto f atTop (nhds 1) := by
  rw [tendsto_order]
  constructor
  · -- For b < 1: eventually f(c) > b
    intro b hb
    obtain ⟨c₀, hc₀⟩ := density_at_infinity ((1 - b) / 2) (by linarith)
    exact eventually_atTop.mpr ⟨max c₀ 0, fun c hc => by
      have h_ge : f c ≥ 1 - (1 - b) / 2 :=
        ge_of_tendsto (hf c (le_trans (le_max_right _ _) hc))
          ((hc₀ c (le_trans (le_max_left _ _) hc)).mono fun N hN => le_of_lt hN)
      linarith⟩
  · -- For b > 1: f(c) ≤ 1 < b always
    intro b hb
    exact eventually_atTop.mpr ⟨0, fun c hc =>
      lt_of_le_of_lt (density_function_le_one c (f c) (hf c hc)) hb⟩
