import Mathlib
import Proofs.BetaCentralBinomialExplicitRate

/-
# The Second-Order Term of the Diagonal Beta Correction: `q n = 1 + 1/(8n) + O(1/n²)`

## What This Proves (answering `beta-central-binomial-explicit-rate` OQ-02)

The parent entry (`beta-central-binomial-explicit-rate`) proves the effective
*first-order* rate `q n = 1 + O(1/n)` for the multiplicative correction

  `q n = stirlingSeq(n)² / (√π · stirlingSeq(2n))`,   i.e.   `B(n+1,n+1) = T n · q n`,

bracketing it between two `O(1/n)` exponentials.  OQ-02 asks whether the
telescoping tail-bound technique extends to a genuine asymptotic **expansion**
`q n = 1 + c₁/n + c₂/n² + ⋯` with *effective, machine-checked* remainder terms.

This entry supplies the first nontrivial coefficient with an effective remainder.

* **`stirlingLogDev_bracket`** (main new infrastructure): a *sharp* two-sided
  bracket for the Stirling log-deviation,
    `1/(12j) - 1/(12j²) ≤ log stirlingSeq(j) - log√π ≤ 1/(12j)`   (`j ≥ 1`).
  The upper bound `≤ 1/(12j)` is **exact to leading order** (Mathlib only packages
  the far cruder `≤ 1/(4j)` telescoping bound, and the parent entry only reaches
  `1/(4j)`); this identifies the true leading coefficient `1/12`.

* **`correction_log_second_order`** (the OQ-02 answer): for `n ≥ 1`,
    `|log (q n) - 1/(8n)| ≤ 1/(6 n²)`.
  So `c₁ = 1/8` with an explicit `O(1/n²)` remainder — a real advance over the
  parent's `1 + O(1/n)`.

* **`correction_log_isBigO_second_order`** (clean Landau form):
    `(fun n => log (q n) - 1/(8n)) =O[atTop] (fun n => 1/n²)`.

Part 4 pushes this one order further.  Sharpening the *lower* Stirling bracket from
`1/(12j) - 1/(12j²)` to the cubic `1/(12j) - 1/(144 j³)` (matching the exact upper
bound `1/(12j)` to order `1/j³`) yields:

* **`correction_log_third_order`** (the `c₂ = 0` answer): for `n ≥ 1`,
    `|log (q n) - 1/(8n)| ≤ 1/(6 n²)` is upgraded to `≤ 1/(72 n³)`.
  So the asymptotic expansion `q n = 1 + c₁/n + c₂/n² + ⋯` has **`c₂ = 0`** — no
  genuine `1/n²` term — and the first correction beyond `1/(8n)` lives at order `1/n³`.

* **`correction_log_isBigO_third_order`**:
    `(fun n => log (q n) - 1/(8n)) =O[atTop] (fun n => 1/n³)`.

## The Engine

The exact second-order coefficient is unlocked by Mathlib's **exact per-step
series** `Stirling.log_stirlingSeq_diff_hasSum`:

  `log stirlingSeq(m+1) - log stirlingSeq(m+2)
      = Σ_{k≥0} (1/(2k+3))·x^{2k+2}`,   `x = 1/(2m+3)`.

Bounding this positive series two-sidedly:

  * termwise geometric majorant `1/(2k+3) ≤ 1/3` gives the **exact** upper
    per-step bound `≤ (x²/3)/(1-x²) = 1/(12(m+1)(m+2))`, which *telescopes
    exactly* to `1/(12j)`;
  * the single leading term `x²/3 = 1/(3(2m+3)²)` gives the lower per-step bound,
    whose deficit from the telescoping model is `O(1/i⁴)` — again telescoping,
    to an `O(1/j²)` correction.

Feeding `log (q n) = 2·S(n) - S(2n)` (with `S(j) = log stirlingSeq(j) - log√π`,
the parent's `log_correction_eq`) the bracket collapses the leading `1/(12·)`
contributions to exactly `1/(8n)`, with the remainders combining to `O(1/n²)`.
-/

open Filter Asymptotics
open scoped Topology Real Nat

namespace BetaDiagSecondOrder

open Stirling

/-! ### Part 1 — Sharp per-step bounds from the exact Stirling series -/

/-- **Exact upper per-step bound (new).**  For every `m`,
`log stirlingSeq(m+1) - log stirlingSeq(m+2) ≤ 1/(12(m+1)) - 1/(12(m+2))`.

The geometric majorant of the per-step series `Σ (1/(2k+3))·(x²)^{k+1}` (with
`x = 1/(2(m+1)+1)`) sums to exactly `(x²/3)/(1-x²) = 1/(12(m+1)(m+2))`. -/
lemma diff_upper (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + 2))
      ≤ 1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + 2)) := by
  have hHS := Stirling.log_stirlingSeq_diff_hasSum m
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hHS
  set t : ℝ := (m : ℝ) + 1 with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have ht1p : (0 : ℝ) < t + 1 := by linarith
  have hden : (0 : ℝ) < 2 * t + 1 := by linarith
  set x : ℝ := 1 / (2 * t + 1) with hx
  set y : ℝ := x ^ 2 with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hy_eq : y = 1 / (2 * t + 1) ^ 2 := by rw [hy, hx, div_pow]; norm_num
  have hylt1 : y < 1 := by
    rw [hy_eq, div_lt_one (by positivity)]; nlinarith [ht0]
  -- rewrite the summand into a clean form
  have hfe : (fun k : ℕ => 1 / (2 * ((k + 1 : ℕ) : ℝ) + 1) * y ^ (k + 1))
      = (fun k : ℕ => 1 / (2 * ((k : ℝ) + 1) + 1) * y ^ (k + 1)) := by
    funext k; push_cast; ring
  rw [hfe] at hHS
  -- geometric series Σ yᵏ = (1-y)⁻¹, then multiply by 1/3·y
  have hgeo : HasSum (fun k : ℕ => y ^ k) (1 - y)⁻¹ :=
    hasSum_geometric_of_lt_one hypos.le hylt1
  have hgeo' : HasSum (fun k : ℕ => (1 / 3 * y) * y ^ k) ((1 / 3 * y) * (1 - y)⁻¹) :=
    hgeo.mul_left _
  -- termwise domination
  have hterm : ∀ k : ℕ,
      1 / (2 * ((k : ℝ) + 1) + 1) * y ^ (k + 1) ≤ (1 / 3 * y) * y ^ k := by
    intro k
    have hyk : (0 : ℝ) ≤ y ^ k := by positivity
    have hcoef : 1 / (2 * ((k : ℝ) + 1) + 1) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    calc 1 / (2 * ((k : ℝ) + 1) + 1) * y ^ (k + 1)
        = 1 / (2 * ((k : ℝ) + 1) + 1) * y * y ^ k := by rw [pow_succ]; ring
      _ ≤ 1 / 3 * y * y ^ k := by
            apply mul_le_mul_of_nonneg_right _ hyk
            exact mul_le_mul_of_nonneg_right hcoef hypos.le
      _ = (1 / 3 * y) * y ^ k := by ring
  have hle := hasSum_le hterm hHS hgeo'
  -- evaluate the geometric majorant to 1/(12t(t+1))
  have hkey : 1 / 3 * y = (1 / (12 * t * (t + 1))) * (1 - y) := by
    rw [hy_eq]; field_simp; ring
  have h1y_ne : (1 : ℝ) - y ≠ 0 := by linarith [hylt1]
  have hval : (1 / 3 * y) * (1 - y)⁻¹ = 1 / (12 * t * (t + 1)) := by
    calc (1 / 3 * y) * (1 - y)⁻¹
        = ((1 / (12 * t * (t + 1))) * (1 - y)) * (1 - y)⁻¹ := by rw [hkey]
      _ = 1 / (12 * t * (t + 1)) * ((1 - y) * (1 - y)⁻¹) := by ring
      _ = 1 / (12 * t * (t + 1)) * 1 := by rw [mul_inv_cancel₀ h1y_ne]
      _ = 1 / (12 * t * (t + 1)) := by ring
  rw [hval] at hle
  have hsplit : (1 : ℝ) / (12 * t * (t + 1)) = 1 / (12 * t) - 1 / (12 * (t + 1)) := by
    field_simp; ring
  rw [hsplit] at hle
  have ht2 : t + 1 = (m : ℝ) + 2 := by rw [ht]; ring
  rw [ht2] at hle
  exact hle

/-- **Lower per-step leading term (new).**  For every `m`, the per-step drop is at
least its leading series term `x²/3 = 1/(3(2(m+1)+1)²)`. -/
lemma diff_lower_leading (m : ℕ) :
    1 / (3 * (2 * ((m : ℝ) + 1) + 1) ^ 2)
      ≤ Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + 2)) := by
  have hHS := Stirling.log_stirlingSeq_diff_hasSum m
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hHS
  set t : ℝ := (m : ℝ) + 1 with ht
  set x : ℝ := 1 / (2 * t + 1) with hx
  set y : ℝ := x ^ 2 with hy
  have hypos : 0 < y := by rw [hy]; positivity
  have hfe : (fun k : ℕ => 1 / (2 * ((k + 1 : ℕ) : ℝ) + 1) * y ^ (k + 1))
      = (fun k : ℕ => 1 / (2 * ((k : ℝ) + 1) + 1) * y ^ (k + 1)) := by
    funext k; push_cast; ring
  rw [hfe] at hHS
  have hnonneg : ∀ k : ℕ, k ≠ 0 →
      0 ≤ 1 / (2 * ((k : ℝ) + 1) + 1) * y ^ (k + 1) := by
    intro k _; positivity
  have h0 := le_hasSum hHS 0 hnonneg
  have hy_eq : y = 1 / (2 * t + 1) ^ 2 := by rw [hy, hx, div_pow]; norm_num
  -- `le_hasSum` already β-reduces the `k = 0` term in `h0`; rewrite it in place.
  have hbeta : 1 / (2 * (((0 : ℕ) : ℝ) + 1) + 1) * y ^ (0 + 1)
      = 1 / (3 * (2 * t + 1) ^ 2) := by
    rw [hy_eq]
    simp only [Nat.cast_zero, zero_add, pow_one]
    rw [div_mul_div_comm]
    norm_num
  rw [hbeta] at h0
  exact h0

/-- **Lower per-step bound in telescoping form (new).**  For every `m`, with
`t = (m:ℝ)+1`,
`log stirlingSeq(m+1) - log stirlingSeq(m+2)
    ≥ (1/(12t) - 1/(12(t+1))) - (1/12)(1/t² - 1/(t+1)²)`.

The correction majorant telescopes to an `O(1/j²)` tail. -/
lemma diff_lower (m : ℕ) :
    (1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + 2)))
        - (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2 - 1 / ((m : ℝ) + 2) ^ 2)
      ≤ Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + 2)) := by
  have hlead := diff_lower_leading m
  set t : ℝ := (m : ℝ) + 1 with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have ht1p : (0 : ℝ) < t + 1 := by linarith
  have hden : (0 : ℝ) < 2 * t + 1 := by linarith
  have ht2 : (m : ℝ) + 2 = t + 1 := by rw [ht]; ring
  rw [ht2]
  have hne0 : t ≠ 0 := ht0.ne'
  have hne1 : t + 1 ≠ 0 := ht1p.ne'
  have hne2 : 2 * t + 1 ≠ 0 := hden.ne'
  have halg :
      (1 / (12 * t) - 1 / (12 * (t + 1))) - (1 / 12) * (1 / t ^ 2 - 1 / (t + 1) ^ 2)
        ≤ 1 / (3 * (2 * t + 1) ^ 2) := by
    rw [← sub_nonneg]
    have hEq : 1 / (3 * (2 * t + 1) ^ 2)
          - ((1 / (12 * t) - 1 / (12 * (t + 1))) - (1 / 12) * (1 / t ^ 2 - 1 / (t + 1) ^ 2))
        = ((2 * t + 1) ^ 3 - t * (t + 1))
            / (12 * t ^ 2 * (t + 1) ^ 2 * (2 * t + 1) ^ 2) := by
      field_simp; ring
    rw [hEq]
    apply div_nonneg
    · nlinarith [ht0, sq_nonneg t, sq_nonneg (t - 1)]
    · positivity
  linarith [hlead, halg]

/-! ### Part 2 — Telescoping to the sharp Stirling deviation bracket -/

/-- Telescoping sum of the upper model. -/
private lemma tel_upper (m N : ℕ) :
    (∑ j ∈ Finset.range N,
        (1 / (12 * ((m : ℝ) + j + 1)) - 1 / (12 * ((m : ℝ) + j + 2))))
      = 1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1)) := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Telescoping sum of the correction model. -/
private lemma tel_corr (m N : ℕ) :
    (∑ j ∈ Finset.range N,
        ((1 / 12) * (1 / ((m : ℝ) + j + 1) ^ 2 - 1 / ((m : ℝ) + j + 2) ^ 2)))
      = (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2 - 1 / ((m : ℝ) + N + 1) ^ 2) := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `1/(12(m+N+1)) → 0`. -/
private lemma tendsto_tail_zero (m : ℕ) :
    Tendsto (fun N : ℕ => 1 / (12 * ((m : ℝ) + N + 1))) atTop (𝓝 0) := by
  have hden : Tendsto (fun N : ℕ => 12 * ((m : ℝ) + N + 1)) atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 12)
    apply Filter.tendsto_atTop_add_const_right
    apply Filter.tendsto_atTop_add_const_left
    exact tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden

/-- **Upper bound of the sharp bracket.**  For every `m`,
`log stirlingSeq(m+1) - log√π ≤ 1/(12(m+1))`. -/
lemma stirlingLogDev_upper (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π)
      ≤ 1 / (12 * ((m : ℝ) + 1)) := by
  set g : ℕ → ℝ := fun j => Real.log (Stirling.stirlingSeq (m + j + 1)) with hg
  have hsum : ∀ N : ℕ, (∑ j ∈ Finset.range N, (g j - g (j + 1)))
      = Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + N + 1)) := by
    intro N; rw [Finset.sum_range_sub' g N]
  have hbound : ∀ N : ℕ, (∑ j ∈ Finset.range N, (g j - g (j + 1))) ≤ 1 / (12 * ((m : ℝ) + 1)) := by
    intro N
    have hle : (∑ j ∈ Finset.range N, (g j - g (j + 1)))
        ≤ ∑ j ∈ Finset.range N,
            (1 / (12 * ((m : ℝ) + j + 1)) - 1 / (12 * ((m : ℝ) + j + 2))) := by
      apply Finset.sum_le_sum
      intro j _
      have h := diff_upper (m + j)
      have hc1 : ((m + j : ℕ) : ℝ) + 1 = (m : ℝ) + j + 1 := by push_cast; ring
      have hc2 : ((m + j : ℕ) : ℝ) + 2 = (m : ℝ) + j + 2 := by push_cast; ring
      rw [hc1, hc2] at h
      simpa only [hg] using h
    rw [tel_upper m N] at hle
    have h0 : (0 : ℝ) ≤ 1 / (12 * ((m : ℝ) + N + 1)) := by positivity
    linarith
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have htend_arg : Tendsto (fun N : ℕ => m + N + 1) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have htend_s : Tendsto (fun N : ℕ => Stirling.stirlingSeq (m + N + 1)) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp htend_arg
  have htend_log : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq (m + N + 1))) atTop
      (𝓝 (Real.log (Real.sqrt π))) :=
    (Real.continuousAt_log hπ.ne').tendsto.comp htend_s
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (g j - g (j + 1))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π))) := by
    have := (tendsto_const_nhds (x := Real.log (Stirling.stirlingSeq (m + 1)))).sub htend_log
    refine this.congr ?_
    intro N; rw [hsum N]
  exact le_of_tendsto' htend hbound

/-- **Lower bound of the sharp bracket.**  For every `m`,
`1/(12(m+1)) - 1/(12(m+1)²) ≤ log stirlingSeq(m+1) - log√π`. -/
lemma stirlingLogDev_lower (m : ℕ) :
    1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + 1) ^ 2)
      ≤ Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π) := by
  set g : ℕ → ℝ := fun j => Real.log (Stirling.stirlingSeq (m + j + 1)) with hg
  have hsum : ∀ N : ℕ, (∑ j ∈ Finset.range N, (g j - g (j + 1)))
      = Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + N + 1)) := by
    intro N; rw [Finset.sum_range_sub' g N]
  have hbound : ∀ N : ℕ,
      (1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1)))
          - (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2)
        ≤ (∑ j ∈ Finset.range N, (g j - g (j + 1))) := by
    intro N
    have hle : (∑ j ∈ Finset.range N,
          ((1 / (12 * ((m : ℝ) + j + 1)) - 1 / (12 * ((m : ℝ) + j + 2)))
            - (1 / 12) * (1 / ((m : ℝ) + j + 1) ^ 2 - 1 / ((m : ℝ) + j + 2) ^ 2)))
        ≤ (∑ j ∈ Finset.range N, (g j - g (j + 1))) := by
      apply Finset.sum_le_sum
      intro j _
      have h := diff_lower (m + j)
      have hc1 : ((m + j : ℕ) : ℝ) + 1 = (m : ℝ) + j + 1 := by push_cast; ring
      have hc2 : ((m + j : ℕ) : ℝ) + 2 = (m : ℝ) + j + 2 := by push_cast; ring
      rw [hc1, hc2] at h
      simpa only [hg] using h
    rw [Finset.sum_sub_distrib, tel_upper m N, tel_corr m N] at hle
    have hmono : (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2 - 1 / ((m : ℝ) + N + 1) ^ 2)
        ≤ (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2) := by
      have : (0 : ℝ) ≤ 1 / ((m : ℝ) + N + 1) ^ 2 := by positivity
      nlinarith [this]
    linarith
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have htend_arg : Tendsto (fun N : ℕ => m + N + 1) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have htend_s : Tendsto (fun N : ℕ => Stirling.stirlingSeq (m + N + 1)) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp htend_arg
  have htend_log : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq (m + N + 1))) atTop
      (𝓝 (Real.log (Real.sqrt π))) :=
    (Real.continuousAt_log hπ.ne').tendsto.comp htend_s
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (g j - g (j + 1))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π))) := by
    have := (tendsto_const_nhds (x := Real.log (Stirling.stirlingSeq (m + 1)))).sub htend_log
    refine this.congr ?_
    intro N; rw [hsum N]
  -- the partial lower bounds tend to 1/(12(m+1)) - (1/12)/(m+1)²
  have htendM : Tendsto (fun N : ℕ =>
      1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1))) atTop
      (𝓝 (1 / (12 * ((m : ℝ) + 1)) - 0)) :=
    tendsto_const_nhds.sub (tendsto_tail_zero m)
  have htend_lb : Tendsto (fun N : ℕ =>
      (1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1)))
        - (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2)) atTop
      (𝓝 ((1 / (12 * ((m : ℝ) + 1)) - 0) - (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2))) :=
    htendM.sub_const _
  have hfinal := le_of_tendsto_of_tendsto' htend_lb htend hbound
  have hsimp : (1 / (12 * ((m : ℝ) + 1)) - 0) - (1 / 12) * (1 / ((m : ℝ) + 1) ^ 2)
      = 1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + 1) ^ 2) := by
    rw [sub_zero, div_mul_div_comm, one_mul]
  rw [hsimp] at hfinal
  exact hfinal

/-- **Sharp Stirling deviation bracket (new).**  For `j ≥ 1`,
`1/(12j) - 1/(12j²) ≤ log stirlingSeq(j) - log√π ≤ 1/(12j)`. -/
theorem stirlingLogDev_bracket (j : ℕ) (hj : 1 ≤ j) :
    1 / (12 * (j : ℝ)) - 1 / (12 * (j : ℝ) ^ 2)
        ≤ Real.log (Stirling.stirlingSeq j) - Real.log (Real.sqrt π) ∧
    Real.log (Stirling.stirlingSeq j) - Real.log (Real.sqrt π) ≤ 1 / (12 * (j : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h := stirlingLogDev_lower m; rw [hc]; exact h
  · have h := stirlingLogDev_upper m; rw [hc]; exact h

/-! ### Part 3 — The second-order correction term `q n = 1 + 1/(8n) + O(1/n²)` -/

open BetaDiagExplicitRate

/-- **Main result (OQ-02 answer): effective second-order term.**  For `n ≥ 1`,
`|log (q n) - 1/(8n)| ≤ 1/(6 n²)`.

This upgrades the parent's `log (q n) = O(1/n)` to the identified leading
coefficient `1/8` with an effective `O(1/n²)` remainder. -/
theorem correction_log_second_order (n : ℕ) (hn : 1 ≤ n) :
    |Real.log (correction n) - 1 / (8 * (n : ℝ))| ≤ 1 / (6 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := hn0.ne'
  obtain ⟨hSn_lo, hSn_hi⟩ := stirlingLogDev_bracket n hn
  obtain ⟨hS2n_lo, hS2n_hi⟩ := stirlingLogDev_bracket (2 * n) (by omega)
  have hcast2n : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hcast2n] at hS2n_lo hS2n_hi
  rw [log_correction_eq n hn]
  set Sn : ℝ := Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt π) with hSn
  set S2n : ℝ := Real.log (Stirling.stirlingSeq (2 * n)) - Real.log (Real.sqrt π) with hS2n
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- lower
    have e1 : (2 : ℝ) * (1 / (12 * (n : ℝ)) - 1 / (12 * (n : ℝ) ^ 2))
        - 1 / (12 * (2 * (n : ℝ))) - 1 / (8 * (n : ℝ)) = -(1 / (6 * (n : ℝ) ^ 2)) := by
      field_simp; ring
    linarith [hSn_lo, hS2n_hi, e1]
  · -- upper
    have e2 : (2 : ℝ) * (1 / (12 * (n : ℝ)))
        - (1 / (12 * (2 * (n : ℝ))) - 1 / (12 * (2 * (n : ℝ)) ^ 2))
        - 1 / (8 * (n : ℝ)) = 1 / (48 * (n : ℝ) ^ 2) := by
      field_simp; ring
    have h48le6 : (1 : ℝ) / (48 * (n : ℝ) ^ 2) ≤ 1 / (6 * (n : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg (n : ℝ), hn0]
    linarith [hSn_hi, hS2n_lo, e2, h48le6]

/-- **Clean Landau form.**  `log (q n) - 1/(8n) = O(1/n²)`. -/
theorem correction_log_isBigO_second_order :
    (fun n : ℕ => Real.log (correction n) - 1 / (8 * (n : ℝ))) =O[atTop]
      (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / 6, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hb := correction_log_second_order n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ 2)]
  calc |Real.log (correction n) - 1 / (8 * (n : ℝ))| ≤ 1 / (6 * (n : ℝ) ^ 2) := hb
    _ = 1 / 6 * (1 / (n : ℝ) ^ 2) := by ring

/-! ### Part 4 — The `1/n²` coefficient vanishes: `q n = 1 + 1/(8n) + O(1/n³)`

The second-order result above brackets `log (q n) - 1/(8n)` by `O(1/n²)`.  Does the
expansion *continue* — is there a genuine `c₂/n²` term?  The true Stirling deviation
`S(j) = log stirlingSeq(j) - log√π = 1/(12j) - 1/(360 j³) + ⋯` carries **no** `1/j²`
term, so `c₂ = 0` and the next correction sits at `1/n³`.

We prove this by *sharpening the lower bracket*.  The per-step deficit of the exact
upper model from the leading series term is
  `1/(12 i(i+1)) - 1/(3(2i+1)²) = 1/(12 i(i+1)(2i+1)²)`,
which is dominated by the telescoping cubic model `(1/144)(1/i³ - 1/(i+1)³)` — the
inequality collapses to `0 ≤ 7·i(i+1) + 1`.  Telescoping this `O(1/i⁴)` deficit gives
the cubic lower bracket `S(j) ≥ 1/(12j) - 1/(144 j³)`, matching the exact upper bound
`S(j) ≤ 1/(12j)` to order `1/j³`.  Feeding `log (q n) = 2·S(n) - S(2n)` collapses the
`1/n²` contributions to exactly `0`. -/

/-- **Sharpened lower per-step bound (new).**  For every `m`, the per-step drop exceeds
the exact upper model corrected by a *cubic* telescoping term:
`step ≥ (1/(12(m+1)) - 1/(12(m+2))) - (1/144)(1/(m+1)³ - 1/(m+2)³)`.

The correction majorant telescopes to an `O(1/j³)` tail — one order sharper than
`diff_lower`.  The pointwise inequality reduces to `0 ≤ 7·t(t+1) + 1`. -/
lemma diff_lower_cubic (m : ℕ) :
    (1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + 2)))
        - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3 - 1 / ((m : ℝ) + 2) ^ 3)
      ≤ Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + 2)) := by
  have hlead := diff_lower_leading m
  set t : ℝ := (m : ℝ) + 1 with ht
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have ht1p : (0 : ℝ) < t + 1 := by linarith
  have hden : (0 : ℝ) < 2 * t + 1 := by linarith
  have ht2 : (m : ℝ) + 2 = t + 1 := by rw [ht]; ring
  rw [ht2]
  have hne0 : t ≠ 0 := ht0.ne'
  have hne1 : t + 1 ≠ 0 := ht1p.ne'
  have hne2 : 2 * t + 1 ≠ 0 := hden.ne'
  have halg :
      (1 / (12 * t) - 1 / (12 * (t + 1))) - (1 / 144) * (1 / t ^ 3 - 1 / (t + 1) ^ 3)
        ≤ 1 / (3 * (2 * t + 1) ^ 2) := by
    rw [← sub_nonneg]
    have hEq : 1 / (3 * (2 * t + 1) ^ 2)
          - ((1 / (12 * t) - 1 / (12 * (t + 1)))
              - (1 / 144) * (1 / t ^ 3 - 1 / (t + 1) ^ 3))
        = (7 * (t * (t + 1)) + 1)
            / (144 * t ^ 3 * (t + 1) ^ 3 * (2 * t + 1) ^ 2) := by
      field_simp; ring
    rw [hEq]
    apply div_nonneg
    · nlinarith [ht0, mul_pos ht0 ht1p]
    · positivity
  linarith [hlead, halg]

/-- Telescoping sum of the cubic correction model. -/
private lemma tel_cubic (m N : ℕ) :
    (∑ j ∈ Finset.range N,
        ((1 / 144) * (1 / ((m : ℝ) + j + 1) ^ 3 - 1 / ((m : ℝ) + j + 2) ^ 3)))
      = (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3 - 1 / ((m : ℝ) + N + 1) ^ 3) := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **Cubic lower bound of the deviation (new).**  For every `m`,
`1/(12(m+1)) - (1/144)/(m+1)³ ≤ log stirlingSeq(m+1) - log√π`. -/
lemma stirlingLogDev_lower_cubic (m : ℕ) :
    1 / (12 * ((m : ℝ) + 1)) - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3)
      ≤ Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π) := by
  set g : ℕ → ℝ := fun j => Real.log (Stirling.stirlingSeq (m + j + 1)) with hg
  have hsum : ∀ N : ℕ, (∑ j ∈ Finset.range N, (g j - g (j + 1)))
      = Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Stirling.stirlingSeq (m + N + 1)) := by
    intro N; rw [Finset.sum_range_sub' g N]
  have hbound : ∀ N : ℕ,
      (1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1)))
          - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3)
        ≤ (∑ j ∈ Finset.range N, (g j - g (j + 1))) := by
    intro N
    have hle : (∑ j ∈ Finset.range N,
          ((1 / (12 * ((m : ℝ) + j + 1)) - 1 / (12 * ((m : ℝ) + j + 2)))
            - (1 / 144) * (1 / ((m : ℝ) + j + 1) ^ 3 - 1 / ((m : ℝ) + j + 2) ^ 3)))
        ≤ (∑ j ∈ Finset.range N, (g j - g (j + 1))) := by
      apply Finset.sum_le_sum
      intro j _
      have h := diff_lower_cubic (m + j)
      have hc1 : ((m + j : ℕ) : ℝ) + 1 = (m : ℝ) + j + 1 := by push_cast; ring
      have hc2 : ((m + j : ℕ) : ℝ) + 2 = (m : ℝ) + j + 2 := by push_cast; ring
      rw [hc1, hc2] at h
      simpa only [hg] using h
    rw [Finset.sum_sub_distrib, tel_upper m N, tel_cubic m N] at hle
    have hmono : (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3 - 1 / ((m : ℝ) + N + 1) ^ 3)
        ≤ (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3) := by
      have : (0 : ℝ) ≤ 1 / ((m : ℝ) + N + 1) ^ 3 := by positivity
      nlinarith [this]
    linarith
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have htend_arg : Tendsto (fun N : ℕ => m + N + 1) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have htend_s : Tendsto (fun N : ℕ => Stirling.stirlingSeq (m + N + 1)) atTop (𝓝 (Real.sqrt π)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp htend_arg
  have htend_log : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq (m + N + 1))) atTop
      (𝓝 (Real.log (Real.sqrt π))) :=
    (Real.continuousAt_log hπ.ne').tendsto.comp htend_s
  have htend : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, (g j - g (j + 1))) atTop
      (𝓝 (Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt π))) := by
    have := (tendsto_const_nhds (x := Real.log (Stirling.stirlingSeq (m + 1)))).sub htend_log
    refine this.congr ?_
    intro N; rw [hsum N]
  have htendM : Tendsto (fun N : ℕ =>
      1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1))) atTop
      (𝓝 (1 / (12 * ((m : ℝ) + 1)) - 0)) :=
    tendsto_const_nhds.sub (tendsto_tail_zero m)
  have htend_lb : Tendsto (fun N : ℕ =>
      (1 / (12 * ((m : ℝ) + 1)) - 1 / (12 * ((m : ℝ) + N + 1)))
        - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3)) atTop
      (𝓝 ((1 / (12 * ((m : ℝ) + 1)) - 0) - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3))) :=
    htendM.sub_const _
  have hfinal := le_of_tendsto_of_tendsto' htend_lb htend hbound
  have hsimp : (1 / (12 * ((m : ℝ) + 1)) - 0) - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3)
      = 1 / (12 * ((m : ℝ) + 1)) - (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3) := by
    rw [sub_zero]
  rw [hsimp] at hfinal
  exact hfinal

/-- **Cubic Stirling deviation bracket (new).**  For `j ≥ 1`,
`1/(12j) - 1/(144 j³) ≤ log stirlingSeq(j) - log√π ≤ 1/(12j)`.

This is one order sharper on the lower side than `stirlingLogDev_bracket`: the slack
drops from `1/(12j²)` to `1/(144 j³)`, pinning `S(j) = 1/(12j) + O(1/j³)`. -/
theorem stirlingLogDev_bracket_cubic (j : ℕ) (hj : 1 ≤ j) :
    1 / (12 * (j : ℝ)) - 1 / (144 * (j : ℝ) ^ 3)
        ≤ Real.log (Stirling.stirlingSeq j) - Real.log (Real.sqrt π) ∧
    Real.log (Stirling.stirlingSeq j) - Real.log (Real.sqrt π) ≤ 1 / (12 * (j : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h := stirlingLogDev_lower_cubic m
    rw [hc]
    have hconv : (1 / 144) * (1 / ((m : ℝ) + 1) ^ 3) = 1 / (144 * ((m : ℝ) + 1) ^ 3) := by
      rw [div_mul_div_comm, one_mul]
    rw [hconv] at h
    exact h
  · have h := stirlingLogDev_upper m; rw [hc]; exact h

/-- **Main result (OQ-02, third order): the `1/n²` coefficient of `log (q n)` vanishes.**
For `n ≥ 1`,
`|log (q n) - 1/(8n)| ≤ 1/(72 n³)`.

Upgrading the second-order `O(1/n²)` bound to `O(1/n³)` shows the asymptotic expansion
`q n = 1 + c₁/n + c₂/n² + ⋯` has `c₂ = 0`: the multiplicative diagonal Beta correction
has no genuine `1/n²` term, and the first correction beyond `1/(8n)` sits at order
`1/n³`. -/
theorem correction_log_third_order (n : ℕ) (hn : 1 ≤ n) :
    |Real.log (correction n) - 1 / (8 * (n : ℝ))| ≤ 1 / (72 * (n : ℝ) ^ 3) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnz : (n : ℝ) ≠ 0 := hn0.ne'
  obtain ⟨hSn_lo, hSn_hi⟩ := stirlingLogDev_bracket_cubic n hn
  obtain ⟨hS2n_lo, hS2n_hi⟩ := stirlingLogDev_bracket_cubic (2 * n) (by omega)
  have hcast2n : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  rw [hcast2n] at hS2n_lo hS2n_hi
  rw [log_correction_eq n hn]
  set Sn : ℝ := Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt π) with hSn
  set S2n : ℝ := Real.log (Stirling.stirlingSeq (2 * n)) - Real.log (Real.sqrt π) with hS2n
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- lower
    have e1 : (2 : ℝ) * (1 / (12 * (n : ℝ)) - 1 / (144 * (n : ℝ) ^ 3))
        - 1 / (12 * (2 * (n : ℝ))) - 1 / (8 * (n : ℝ)) = -(1 / (72 * (n : ℝ) ^ 3)) := by
      field_simp; ring
    linarith [hSn_lo, hS2n_hi, e1]
  · -- upper
    have e2 : (2 : ℝ) * (1 / (12 * (n : ℝ)))
        - (1 / (12 * (2 * (n : ℝ))) - 1 / (144 * (2 * (n : ℝ)) ^ 3))
        - 1 / (8 * (n : ℝ)) = 1 / (1152 * (n : ℝ) ^ 3) := by
      field_simp; ring
    have h1152le72 : (1 : ℝ) / (1152 * (n : ℝ) ^ 3) ≤ 1 / (72 * (n : ℝ) ^ 3) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [hn0, pow_pos hn0 3]
    linarith [hSn_hi, hS2n_lo, e2, h1152le72]

/-- **Clean Landau form (third order).**  `log (q n) - 1/(8n) = O(1/n³)`. -/
theorem correction_log_isBigO_third_order :
    (fun n : ℕ => Real.log (correction n) - 1 / (8 * (n : ℝ))) =O[atTop]
      (fun n : ℕ => 1 / (n : ℝ) ^ 3) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1 / 72, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hb := correction_log_third_order n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ 3)]
  calc |Real.log (correction n) - 1 / (8 * (n : ℝ))| ≤ 1 / (72 * (n : ℝ) ^ 3) := hb
    _ = 1 / 72 * (1 / (n : ℝ) ^ 3) := by ring

end BetaDiagSecondOrder
