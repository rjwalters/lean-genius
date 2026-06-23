/-
  Ramanujan Sum Fallacy — OQ-02: Cesàro summation, and Grandi's series sums to 1/2

  The gallery entry `RamanujanSumFallacy` proves that Grandi's series
  `1 − 1 + 1 − 1 + …` is **not** summable in the ordinary (`tsum`) sense — there is
  no convergent value.  Its open question OQ-02 asks: *how would you define Cesàro
  summation in Lean, and show that the Cesàro sum of Grandi's series really is 1/2?*

  This file answers it.

  * `partialSum a n`  — the `n`-th partial sum `∑_{k<n} a k`.
  * `cesaroMean a n`  — the average `(1/n) ∑_{k<n} partialSum a k` of the first `n`
    partial sums (`0` at `n = 0` by the junk-value convention for division).
  * `CesaroSum a L`   — the Cesàro summability predicate: the Cesàro means converge
    to `L`.

  The headline is `grandi_cesaroSum_half : CesaroSum grandi (1/2)`: even though
  Grandi's series diverges in the ordinary sense, its Cesàro means converge to 1/2.
  The computation is explicit — for `n ≥ 1`,

      cesaroMean grandi n = 1/2 − (1 − (−1)ⁿ) / (4n),

  whose error term is squeezed to `0` by `0 ≤ (1−(−1)ⁿ)/(4n) ≤ 1/n`.

  We also record `grandi_cesaroSummable`: Grandi's series is Cesàro-summable even
  though (by the parent file) it is not ordinarily summable — Cesàro summation is a
  strict extension of ordinary convergence on this example.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Hardy, *Divergent Series* (1949), Ch. I; https://erdosproblems.com (Grandi).
-/

import Mathlib

namespace RamanujanFallacyOQ02

open Filter Topology Finset

/-- The `n`-th partial sum `∑_{k<n} a k`. -/
def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, a k

/-- The `n`-th Cesàro mean: the average of the first `n` partial sums. -/
noncomputable def cesaroMean (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, partialSum a k) / (n : ℝ)

/-- `a` is Cesàro-summable to `L` if its Cesàro means converge to `L`. -/
def CesaroSum (a : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto (cesaroMean a) atTop (𝓝 L)

/-- Grandi's series `1 − 1 + 1 − 1 + …`, i.e. `a k = (−1)ᵏ`. -/
def grandi : ℕ → ℝ := fun n => (-1 : ℝ) ^ n

/-- The partial sums of Grandi's series: `∑_{k<n} (−1)ᵏ = (1 − (−1)ⁿ)/2`
    (so `0, 1, 0, 1, …` for `n = 0, 1, 2, 3, …`). -/
theorem partialSum_grandi (n : ℕ) :
    partialSum grandi n = (1 - (-1) ^ n) / 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    unfold partialSum at ih ⊢
    rw [Finset.sum_range_succ, ih]
    simp only [grandi]
    rw [pow_succ]
    ring

/-- The cumulative sum of partial sums: `∑_{k<n} partialSum grandi k = n/2 − (1−(−1)ⁿ)/4`. -/
theorem cesaro_partialsum_grandi (n : ℕ) :
    ∑ k ∈ Finset.range n, partialSum grandi k = (n : ℝ) / 2 - (1 - (-1) ^ n) / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, partialSum_grandi]
    push_cast
    rw [pow_succ]
    ring

/-- **Closed form of the Cesàro mean of Grandi's series** (for `n ≥ 1`):
    `cesaroMean grandi n = 1/2 − (1 − (−1)ⁿ)/(4n)`. -/
theorem cesaroMean_grandi {n : ℕ} (hn : 1 ≤ n) :
    cesaroMean grandi n = 1 / 2 - (1 - (-1) ^ n) / (4 * n) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold cesaroMean
  rw [cesaro_partialsum_grandi]
  field_simp

/-- **Grandi's series is Cesàro-summable to 1/2.**  The Cesàro means converge to
    `1/2` even though the ordinary series diverges: the explicit error term
    `(1 − (−1)ⁿ)/(4n)` is squeezed to `0` by `0 ≤ · ≤ 1/n`. -/
theorem grandi_cesaroSum_half : CesaroSum grandi (1 / 2) := by
  -- The error term tends to 0.
  have herr : Tendsto (fun n : ℕ => (1 - (-1 : ℝ) ^ n) / (4 * n)) atTop (𝓝 0) := by
    refine squeeze_zero ?_ ?_ tendsto_one_div_atTop_nhds_zero_nat
    · -- `0 ≤ (1 − (−1)ⁿ)/(4n)`
      intro n
      have habs : |(-1 : ℝ) ^ n| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
      have h2 : (-1 : ℝ) ^ n ≤ 1 := by linarith [le_abs_self ((-1 : ℝ) ^ n), habs]
      apply div_nonneg
      · linarith
      · positivity
    · -- `(1 − (−1)ⁿ)/(4n) ≤ 1/n`
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have habs : |(-1 : ℝ) ^ n| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
        have h1 : (-1 : ℝ) ^ n ≥ -1 := by linarith [neg_abs_le ((-1 : ℝ) ^ n), habs]
        calc (1 - (-1 : ℝ) ^ n) / (4 * n)
            ≤ 2 / (4 * n) := by gcongr; linarith
          _ = 1 / (2 * n) := by ring
          _ ≤ 1 / n := by gcongr; linarith
  -- The Cesàro means eventually equal `1/2 − error`, which tends to `1/2`.
  have hcong : ∀ᶠ n : ℕ in atTop,
      cesaroMean grandi n = 1 / 2 - (1 - (-1 : ℝ) ^ n) / (4 * n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact cesaroMean_grandi hn
  have hlim := herr.const_sub (1 / 2 : ℝ)
  rw [sub_zero] at hlim
  exact (tendsto_congr' hcong).mpr hlim

/-- Corollary contrasting with the parent file: Grandi's series is Cesàro-summable
    (to `1/2`) even though it is not ordinarily summable.  Cesàro summation is a
    strict extension of ordinary convergence on this example. -/
theorem grandi_cesaroSummable : ∃ L, CesaroSum grandi L :=
  ⟨1 / 2, grandi_cesaroSum_half⟩

end RamanujanFallacyOQ02
