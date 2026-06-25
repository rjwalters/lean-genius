import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

/-
# Dini's Theorem: the Monotonicity Hypothesis Is Necessary

## What This Proves

The parent entry `DiniTheorem` states Dini's theorem and gives two sharpness
witnesses built from `xⁿ` on `[0,1]`: one showing that **continuity of the
pointwise limit** is necessary, and one showing that **compactness of the
domain** is necessary. Both of those examples are *monotone* in `n`, so they
leave open the role of Dini's third hypothesis — that the sequence be monotone.

This file supplies the missing witness for the **monotonicity** hypothesis: an
explicit *moving triangular bump*

  `bump n x = max 0 (1 - |n·x - 1|)`,

a continuous tent function of height `1` peaked at `x = 1/n` and supported on
`[0, 2/n]`. As `n → ∞` the bump slides toward `0` and narrows, so:

* every `bump n` is **continuous** (`bump_continuous`);
* the sequence converges **pointwise** on the compact interval `[0,1]` to the
  **continuous** limit `0` (`bump_tendsto_zero`); and yet
* it does **not** converge uniformly (`bump_not_tendstoUniformlyOn`), because
  the peak `bump n (1/n) = 1` keeps the supremum error pinned at `1`.

The only Dini hypothesis that fails is monotonicity: the sequence
`n ↦ bump n (1/2)` is neither monotone nor antitone
(`bump_not_monotone`, `bump_not_antitone`). So all of compactness, continuity
of each term, and continuity of the limit hold, yet uniform convergence fails —
monotonicity cannot be dropped.

## Relation to Mathlib and the Gallery

Mathlib has Dini's theorem (`tendstoUniformlyOn_of_monotone`-style results) and
the uniform-convergence API, but no packaged counterexample isolating the
monotonicity hypothesis. The parent `DiniTheorem` isolates the other two
hypotheses with `xⁿ`; this entry completes the picture with a moving bump, the
classical example for the necessity of monotonicity.

## Method

The peak value `bump n (1/n) = 1` is an exact computation. Pointwise
convergence is *eventual vanishing*: for `x > 0`, once `n·x ≥ 2` the argument of
the absolute value exceeds `1`, forcing `bump n x = 0`; the point `x = 0` is a
fixed zero. Non-uniformity then follows directly from
`Metric.tendstoUniformlyOn_iff` by exhibiting, for every threshold `N`, the
peak point `1/(N+1)` where the error equals `1`. Non-monotonicity is three
`norm_num` evaluations.
-/

namespace DiniTheoremOQ01

open Real Filter Topology Set

/-- The moving triangular bump: a tent function of height `1`, peaked at
`x = 1/n` and supported on `[0, 2/n]`. -/
noncomputable def bump (n : ℕ) (x : ℝ) : ℝ := max 0 (1 - |(n : ℝ) * x - 1|)

/-- Each bump is continuous. -/
theorem bump_continuous (n : ℕ) : Continuous (bump n) := by
  unfold bump
  exact continuous_const.max (continuous_const.sub
    ((continuous_const.mul continuous_id).sub continuous_const).abs)

/-- Each bump is nonnegative. -/
theorem bump_nonneg (n : ℕ) (x : ℝ) : 0 ≤ bump n x := le_max_left _ _

/-- Each bump is bounded above by its peak height `1`. -/
theorem bump_le_one (n : ℕ) (x : ℝ) : bump n x ≤ 1 := by
  unfold bump
  exact max_le zero_le_one (by linarith [abs_nonneg ((n : ℝ) * x - 1)])

/-- **Peak value.** For `n ≥ 1` the bump attains its maximal value `1` at
`x = 1/n`. This is what keeps the supremum error from shrinking. -/
theorem bump_peak {n : ℕ} (hn : 1 ≤ n) : bump n ((n : ℝ)⁻¹) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn
    positivity
  unfold bump
  rw [mul_inv_cancel₀ hn0]
  norm_num

/-- The bump vanishes once the peak has slid past `x`, i.e. as soon as
`n · x ≥ 2`. -/
theorem bump_eq_zero_of_two_le {n : ℕ} {x : ℝ} (h : 2 ≤ (n : ℝ) * x) :
    bump n x = 0 := by
  unfold bump
  have hge : 1 ≤ |(n : ℝ) * x - 1| := by
    rw [le_abs]; left; linarith
  exact max_eq_left (by linarith)

/-- **Pointwise convergence to the continuous limit `0`.** On `[0,1]` (indeed on
all of `[0,∞)`) the moving bump converges pointwise to `0`. The point `x = 0` is
a fixed zero; for `x > 0` the bump is eventually `0`. -/
theorem bump_tendsto_zero {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => bump n x) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · -- `x = 0`: the bump is identically zero.
    subst hx0
    have : (fun n : ℕ => bump n (0 : ℝ)) = fun _ => (0 : ℝ) := by
      funext n; simp [bump]
    rw [this]; exact tendsto_const_nhds
  · -- `x > 0`: `n · x → ∞`, so eventually `n · x ≥ 2` and the bump is `0`.
    have hxne : x ≠ 0 := ne_of_gt hxpos
    refine Tendsto.congr' ?_ tendsto_const_nhds
    have htop : Tendsto (fun n : ℕ => (n : ℝ) * x) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hxpos
    filter_upwards [htop.eventually_ge_atTop 2] with n hn
    exact (bump_eq_zero_of_two_le hn).symm

/-- **Sharpness witness (monotonicity is necessary).** On the compact interval
`[0,1]` the moving bump is continuous in `x`, converges pointwise to the
*continuous* function `0`, yet does **not** converge uniformly: for every `n`
the peak point `1/n` realises an error of `1`, so the supremum error never drops
below `1/2`. The only failed Dini hypothesis is monotonicity (see
`bump_not_monotone`/`bump_not_antitone`). -/
theorem bump_not_tendstoUniformlyOn :
    ¬ TendstoUniformlyOn bump (fun _ => (0 : ℝ)) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  push_neg
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨N + 1, le_self_add, ((N : ℝ) + 1)⁻¹, ?_, ?_⟩
  · -- the peak point `1/(N+1)` lies in `[0,1]`
    have hpos : 0 < (N : ℝ) + 1 := by positivity
    constructor
    · positivity
    · rw [inv_le_one_iff₀]; right; linarith [Nat.cast_nonneg (α := ℝ) N]
  · -- the error at the peak equals `1`
    have hpeak : bump (N + 1) (((N : ℝ) + 1)⁻¹) = 1 := by
      have h := bump_peak (n := N + 1) (Nat.le_add_left 1 N)
      rwa [Nat.cast_add, Nat.cast_one] at h
    rw [hpeak, Real.dist_eq]
    norm_num

/-- The sequence `n ↦ bump n (1/2)` is **not monotone**: it rises from
`bump 2 (1/2) = 1` and then falls to `bump 4 (1/2) = 0`. -/
theorem bump_not_monotone : ¬ Monotone (fun n : ℕ => bump n (1 / 2 : ℝ)) := by
  intro hmono
  have h := hmono (show 2 ≤ 4 by norm_num)
  -- `bump 2 (1/2) = 1` but `bump 4 (1/2) = 0`, contradicting `2 ≤ 4 → f 2 ≤ f 4`
  norm_num [bump] at h

/-- The sequence `n ↦ bump n (1/2)` is also **not antitone**: it rises from
`bump 1 (1/2) = 1/2` to `bump 2 (1/2) = 1`. Together with `bump_not_monotone`
this shows the family has no monotonicity of either kind — exactly the
hypothesis Dini's theorem cannot do without. -/
theorem bump_not_antitone : ¬ Antitone (fun n : ℕ => bump n (1 / 2 : ℝ)) := by
  intro hanti
  have h := hanti (show 1 ≤ 2 by norm_num)
  -- `bump 1 (1/2) = 1/2` but `bump 2 (1/2) = 1`, contradicting `1 ≤ 2 → f 2 ≤ f 1`
  norm_num [bump] at h

end DiniTheoremOQ01
