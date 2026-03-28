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
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Instances.Real
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
  ∑ i in Finset.range n, seriesTerm a i

/-- m/2^m ≤ (3/4)^m for m ≥ 1. Used for dominated convergence. -/
private theorem div_pow_two_le_three_fourths_pow (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) / (2 : ℝ) ^ m ≤ ((3 : ℝ) / 4) ^ m := by
  -- Equivalent to m ≤ (3/2)^m, proved by induction
  rw [div_le_iff (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
  -- Goal: (m : ℝ) ≤ (3/4)^m * 2^m = (3/2)^m
  have h32 : ((3 : ℝ) / 4) ^ m * (2 : ℝ) ^ m = ((3 : ℝ) / 2) ^ m := by
    rw [← mul_pow]; norm_num
  rw [h32]
  -- Now prove m ≤ (3/2)^m by induction
  suffices ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ ((3 : ℝ) / 2) ^ n from this m hm
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
    intro hk
    rcases Nat.eq_or_gt_of_le hk with rfl | hgt
    · -- k = 0, n = 1: 1 ≤ 3/2
      simp; norm_num
    · -- k ≥ 1: (k+1) ≤ (3/2)^(k+1) = (3/2)^k * (3/2)
      have hk1 : 1 ≤ k := by omega
      have ih_k := ih hk1
      -- (3/2)^k ≥ k ≥ 1, so (3/2)^k ≥ 1
      have hpow_ge_1 : (1 : ℝ) ≤ ((3 : ℝ) / 2) ^ k := le_trans (by norm_cast) ih_k
      calc (↑(k + 1) : ℝ) = ↑k + 1 := by push_cast; ring
        _ ≤ ((3 : ℝ) / 2) ^ k + 1 := by linarith
        _ ≤ ((3 : ℝ) / 2) ^ k + ((3 : ℝ) / 2) ^ k / 2 := by linarith [hpow_ge_1]
        _ = ((3 : ℝ) / 2) ^ k * ((3 : ℝ) / 2) := by ring
        _ = ((3 : ℝ) / 2) ^ (k + 1) := (pow_succ _ _).symm

/-- The function m ↦ m/2^m is summable. -/
private theorem summable_div_pow_two :
    Summable (fun m => (m : ℝ) / (2 : ℝ) ^ m) := by
  apply Summable.of_norm_bounded_eventually (fun m => ((3 : ℝ) / 4) ^ m)
  · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  · rw [Filter.eventually_atTop]
    exact ⟨1, fun m hm => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact div_pow_two_le_three_fourths_pow m hm⟩

/-- The series converges absolutely for any increasing sequence. -/
theorem series_converges (a : IncreasingSeq) :
    ∃ S : ℝ, Tendsto (partialSum a) atTop (𝓝 S) := by
  -- seriesTerm a n = f(a.seq n) where f(m) = m/2^m
  -- Since a.seq is injective (StrictMono) and f is summable,
  -- f ∘ a.seq is summable (Summable.comp_injective)
  have hinj : Function.Injective a.seq := a.strictMono.injective
  have hsum : Summable (fun n => seriesTerm a n) := by
    have := summable_div_pow_two.comp_injective hinj
    convert this using 1
    ext n; simp [seriesTerm]
  exact ⟨∑' n, seriesTerm a n, hsum.hasSum.tendsto_sum_nat⟩

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
  -- If gaps → ∞, then aₙ grows superlinearly
  sorry

/-- Superlogarithmic growth implies fast growth. -/
theorem fastGrowth_of_superlogarithmic (a : IncreasingSeq)
    (h : SuperlogarithmicGrowth a) : FastGrowth a := by
  -- Proof strategy: aₙ/n ≥ C*√(log n · log log n) → ∞
  -- Use tendsto_atTop_mono with the bound from h, then show
  -- C*√(log n · log log n) → ∞ via Tendsto compositions.
  sorry

/- ## Part V: Example Sequences -/

/-- The sequence aₙ = n². -/
def squareSeq : IncreasingSeq where
  seq := fun n => n^2
  strictMono := fun _ _ h => Nat.pow_lt_pow_left h (by norm_num : 1 < 2)

/-- n² satisfies fast growth. -/
theorem squareSeq_fastGrowth : FastGrowth squareSeq := by
  unfold FastGrowth squareSeq
  simp only
  -- n²/n = n → ∞
  have : Tendsto (fun n => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  convert this using 1
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [pow_two]
    field_simp
    ring

/-- n² has gaps → ∞ (since gaps are 2n + 1). -/
theorem squareSeq_gaps : GapsToInfinity squareSeq := by
  unfold GapsToInfinity squareSeq
  simp only
  -- (n+1)² - n² = 2n + 1 → ∞
  have h : ∀ n : ℕ, (n + 1)^2 - n^2 = 2 * n + 1 := by
    intro n; ring
  simp_rw [h]
  -- 2n + 1 → ∞
  apply Tendsto.atTop_add_const
  apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  exact tendsto_natCast_atTop_atTop

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
