/-
  Erdős Problem #260: Irrationality of Series with Sparse Sequences

  Source: https://erdosproblems.com/260
  Status: OPEN

  Statement:
  Let a₁ < a₂ < ⋯ be an increasing sequence of natural numbers such that
  aₙ/n → ∞ as n → ∞. Is the sum ∑ₙ aₙ/2^{aₙ} necessarily irrational?

  Known Results (Erdős):
  - The sum IS irrational if a_{n+1} - aₙ → ∞
  - The sum IS irrational if aₙ ≫ n√(log n · log log n)

  Conjecture (Erdős-Graham):
  The condition limsup(a_{n+1} - aₙ) = ∞ is likely NOT sufficient,
  but no counterexample is known.

  References:
  - [Er74b] Erdős original formulation
  - [ErGr80] Erdős-Graham: Old and New Problems and Results in Combinatorial
    Number Theory
  - [Er81h, p.180]
  - [Er88c, p.103]

  Tags: analysis, irrationality, series, sequences
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos260

open Filter Topology

/- ## Part I: Sequence Properties -/

/-- An increasing sequence of natural numbers. -/
structure IncreasingSeq where
  seq : ℕ → ℕ
  strictMono : StrictMono seq

/-- The ratio aₙ/n tends to infinity. -/
def FastGrowth (a : IncreasingSeq) : Prop :=
  Tendsto (fun n => (a.seq n : ℝ) / n) atTop atTop

/-- The gaps a_{n+1} - aₙ tend to infinity. -/
def GapsToInfinity (a : IncreasingSeq) : Prop :=
  Tendsto (fun n => (a.seq (n + 1) - a.seq n : ℝ)) atTop atTop

/-- Stronger growth condition: aₙ ≫ n√(log n · log log n). -/
def SuperlogarithmicGrowth (a : IncreasingSeq) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in atTop,
    (a.seq n : ℝ) ≥ C * n * Real.sqrt (Real.log n * Real.log (Real.log n))

/- ## Part II: The Series -/

/-- The n-th term of the series: aₙ / 2^{aₙ}. -/
noncomputable def seriesTerm (a : IncreasingSeq) (n : ℕ) : ℝ :=
  (a.seq n : ℝ) / (2 : ℝ) ^ (a.seq n)

/-- The partial sum of the first n terms. -/
noncomputable def partialSum (a : IncreasingSeq) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, seriesTerm a i

/-- The series converges absolutely for any increasing sequence. -/
theorem series_converges (a : IncreasingSeq) :
    ∃ S : ℝ, Tendsto (partialSum a) atTop (𝓝 S) := by
  -- Each term aₙ/2^{aₙ} → 0 rapidly since 2^n grows faster than n
  -- The series is dominated by ∑ n/2^n which converges
  sorry

/-- The limit of the series. -/
noncomputable def seriesSum (a : IncreasingSeq) : ℝ :=
  Classical.choose (series_converges a)

/- ## Part III: Known Irrationality Results -/

/-- Erdős's theorem: gaps → ∞ implies the sum is irrational.

This is a known result from [Er74b]. The key insight is that if the gaps
grow without bound, we can control the denominators in rational approximations
and show that the sum cannot be rational.
-/
theorem irrational_of_gaps_to_infinity (a : IncreasingSeq) (h : GapsToInfinity a) :
    Irrational (seriesSum a) := by
  sorry

/-- Erdős's theorem: superlogarithmic growth implies the sum is irrational.

The condition aₙ ≫ n√(log n · log log n) is sufficient for irrationality.
This follows from more refined estimates on rational approximations.
-/
theorem irrational_of_superlogarithmic (a : IncreasingSeq)
    (h : SuperlogarithmicGrowth a) : Irrational (seriesSum a) := by
  sorry

/- ## Part IV: Basic Properties -/

/-- Fast growth is a weaker condition than gaps → ∞. -/
theorem fastGrowth_of_gapsToInfinity (a : IncreasingSeq) (h : GapsToInfinity a) :
    FastGrowth a := by
  unfold FastGrowth GapsToInfinity at *
  rw [Filter.tendsto_atTop_atTop]
  intro M
  by_cases hM : M ≤ 0
  · exact ⟨1, fun n _hn => le_trans hM (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))⟩
  push_neg at hM
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h (M + 1)
  have hseq : ∀ j : ℕ, (a.seq (N + j) : ℝ) ≥ (a.seq N : ℝ) + ↑j * (M + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hgap : M + 1 ≤ (a.seq (N + j + 1) : ℝ) - (a.seq (N + j) : ℝ) :=
        hN (N + j) (Nat.le_add_right N j)
      have heq : N + (j + 1) = N + j + 1 := by omega
      rw [heq]
      push_cast
      linarith
  use N + ⌈M * (N : ℝ)⌉₊ + 1
  intro n hn
  have hNn : N ≤ n := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hNn
  have hj_nat : ⌈M * (N : ℝ)⌉₊ ≤ j := by omega
  have hj : M * (N : ℝ) ≤ (j : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hj_nat)
  have hn_pos : (0 : ℝ) < (N : ℝ) + (j : ℝ) := by
    exact_mod_cast (show 0 < N + j by omega)
  rw [show ((N + j : ℕ) : ℝ) = (N : ℝ) + (j : ℝ) from by push_cast; ring]
  rw [le_div_iff₀ hn_pos]
  calc M * ((N : ℝ) + (j : ℝ)) = M * (N : ℝ) + M * (j : ℝ) := by ring
    _ ≤ (j : ℝ) + M * (j : ℝ) := by linarith
    _ = (j : ℝ) * (M + 1) := by ring
    _ ≤ (a.seq N : ℝ) + (j : ℝ) * (M + 1) := le_add_of_nonneg_left (Nat.cast_nonneg _)
    _ ≤ (a.seq (N + j) : ℝ) := hseq j

/-- Superlogarithmic growth implies fast growth.
    Proof sketch: aₙ ≥ C·n·√(log n · log log n), so aₙ/n ≥ C·√(log n · log log n) → ∞. -/
theorem fastGrowth_of_superlogarithmic (a : IncreasingSeq)
    (h : SuperlogarithmicGrowth a) : FastGrowth a := by
  obtain ⟨C, hC, hbnd⟩ := h
  unfold FastGrowth
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Real.sqrt x = x ^ (1/2), and x^(1/2) → ∞ as x → ∞
  have hsqrt_log : Filter.Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := by
    have hrpow : Filter.Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 2)) Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    have : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2))
        Filter.atTop Filter.atTop := hrpow.comp hlog
    refine this.congr' ?_
    filter_upwards [hlog.eventually (Filter.eventually_ge_atTop 0)] with n hn
    exact (Real.sqrt_eq_rpow _).symm
  have hCsqrt : Filter.Tendsto (fun n : ℕ => C * Real.sqrt (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop :=
    Tendsto.const_mul_atTop hC hsqrt_log
  have hloglog_ge1 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Real.log (Real.log (n : ℝ)) := by
    filter_upwards [hlog.eventually (Filter.eventually_ge_atTop (Real.exp 1))] with n hn
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.log (n : ℝ)) := Real.log_le_log (Real.exp_pos 1) hn
  have hlb : ∀ᶠ n : ℕ in Filter.atTop,
      C * Real.sqrt (Real.log (n : ℝ)) ≤ (a.seq n : ℝ) / n := by
    filter_upwards [hbnd, Filter.eventually_gt_atTop 0,
                    hlog.eventually (Filter.eventually_ge_atTop 0),
                    hloglog_ge1] with n hn hpos hlog_nn hloglog1
    have hpos_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
    rw [le_div_iff₀ hpos_r]
    calc C * Real.sqrt (Real.log (n : ℝ)) * (n : ℝ)
        ≤ C * Real.sqrt (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) * (n : ℝ) := by
          gcongr
          calc Real.log (n : ℝ) = Real.log (n : ℝ) * 1 := (mul_one _).symm
            _ ≤ Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hloglog1 hlog_nn
      _ = C * (n : ℝ) * Real.sqrt (Real.log (n : ℝ) * Real.log (Real.log (n : ℝ))) := by ring
      _ ≤ (a.seq n : ℝ) := hn
  exact tendsto_atTop_mono' atTop hlb hCsqrt

/- ## Part V: Example Sequences -/

/-- The sequence aₙ = n². -/
def squareSeq : IncreasingSeq where
  seq := fun n => n^2
  strictMono := fun _ _ h => Nat.pow_lt_pow_left h two_ne_zero

/-- n² satisfies fast growth. -/
theorem squareSeq_fastGrowth : FastGrowth squareSeq := by
  unfold FastGrowth squareSeq
  simp only
  -- n²/n = n → ∞
  apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn_pos]
  push_cast
  have : (n : ℝ) * n = (n : ℝ) ^ 2 := by ring
  linarith

/-- n² has gaps → ∞ (since gaps are 2n + 1). -/
theorem squareSeq_gaps : GapsToInfinity squareSeq := by
  unfold GapsToInfinity squareSeq
  simp only
  -- (n+1)² - n² = 2n + 1 → ∞ (in ℝ)
  apply tendsto_atTop_mono' atTop _ (tendsto_atTop_add_const_right atTop 1
    (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
  filter_upwards with n
  push_cast
  nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ) + 1)]

/-- The series for n² is irrational. -/
theorem squareSeq_irrational : Irrational (seriesSum squareSeq) :=
  irrational_of_gaps_to_infinity squareSeq squareSeq_gaps

/- ## Part VI: The Main Conjecture -/

/-- The main conjecture: fast growth alone implies irrationality.

This is Erdős Problem #260. It remains OPEN as of 2025.
The conjecture is that for ANY increasing sequence with aₙ/n → ∞,
the sum ∑ aₙ/2^{aₙ} is irrational.
-/
axiom erdos_260_conjecture : ∀ a : IncreasingSeq, FastGrowth a → Irrational (seriesSum a)

/-- Erdős-Graham speculation: limsup of gaps = ∞ is likely NOT sufficient.

They conjectured there exists a sequence where:
- limsup(a_{n+1} - aₙ) = ∞ (gaps unbounded)
- liminf(a_{n+1} - aₙ) < ∞ (gaps don't tend to ∞)
- The sum is rational

No such example has been found.
-/
def ErdosGrahamCounterexample (a : IncreasingSeq) : Prop :=
  (∀ M : ℝ, ∃ᶠ n in atTop, (a.seq (n + 1) - a.seq n : ℝ) > M) ∧
  (∃ L : ℝ, ∀ᶠ n in atTop, (a.seq (n + 1) - a.seq n : ℝ) ≥ 1 ∧
    ∃ᶠ m in atTop, (a.seq (m + 1) - a.seq m : ℝ) < L) ∧
  ¬Irrational (seriesSum a)

end Erdos260

/- ## Summary

This file formalizes Erdős Problem #260 on the irrationality of series
of the form ∑ aₙ/2^{aₙ} for sparse increasing sequences.

**Status**: OPEN

**What we formalize**:
1. The sequence properties (fast growth, gaps → ∞, superlogarithmic growth)
2. The series definition and convergence
3. Erdős's known partial results (gaps → ∞ or superlogarithmic growth implies irrational)
4. Example: n² gives an irrational sum
5. The main conjecture as an axiom

**Key sorries**:
- `series_converges`: Needs dominated convergence argument
- `irrational_of_gaps_to_infinity`: Erdős's theorem from [Er74b]
- `irrational_of_superlogarithmic`: Stronger version of Erdős's theorem

**What would prove the conjecture**:
A technique to show irrationality using only the growth rate condition aₙ/n → ∞
without additional assumptions on the gap structure.
-/
