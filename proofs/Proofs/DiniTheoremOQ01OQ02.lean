import Mathlib

/-
# Dini's Theorem — OQ-01-OQ-02: The Sharp Modulus of Non-Uniform Convergence of xⁿ on [0,1)

## Research Problem: dini-theorem-oq-01-oq-02

The parent file `DiniTheorem.lean` re-exports Dini's theorem and studies the sharpness of
its hypotheses with the witness sequence `fₙ(x) = xⁿ`.  On the non-compact interval `[0,1)`
this sequence is continuous, monotone (antitone) in `n`, and converges pointwise to the
continuous function `0`, yet the convergence is **not uniform** — Dini fails because the
domain is not compact.  The parent established non-uniformity quantitatively but with a
*non-sharp* bound: it exhibited, for each `n`, a point of `[0,1)` where `xⁿ ≥ 1/2`, so the
uniform error stays `≥ 1/2`.

This file answers the parent's open question OQ-02:

> Does a quantitative refinement hold: on `[0,1)` the uniform distance `sup_x |xⁿ|` stays
> exactly `1`, giving an explicit lower bound on the modulus of non-uniform convergence
> rather than the value `1/2` used here?

**Answer: yes — the sharp modulus is exactly `1`.**

## What is proved

* `pow_image_Ico_isLUB` — for every `n ≥ 1`, the least upper bound of `{ xⁿ : x ∈ [0,1) }`
  is `1`.  The supremum is *not attained* (every `xⁿ < 1`), but it is approached along
  `x = 1 − 1/(k+1) → 1`.
* `pow_sSup_Ico` — hence `sSup { xⁿ : x ∈ [0,1) } = 1`.
* `pow_uniform_error_Ico` — the headline: the uniform error
  `sSup_{x∈[0,1)} |xⁿ − 0| = 1` for every `n ≥ 1`, i.e. the modulus of non-uniform
  convergence is exactly `1`, sharpening the parent's `1/2`.
* `pow_exists_gt_of_lt_one` — the LUB unpacked: for any `c < 1` and `n ≥ 1` there is a point
  of `[0,1)` with `xⁿ > c`.
* `pow_not_tendstoUniformlyOn_Ico_sharp` — the sharpened non-uniformity: the convergence
  fails to be uniform with **any** threshold `c ∈ (0,1)`, not merely `1/2`.

The point is that `1` is the *exact* supremum: it cannot be improved (each `xⁿ < 1`, so no
value `> 1` is even an upper bound, and no value `< 1` is an upper bound either).

Tags: analysis, dini, uniform-convergence, supremum, sharpness, wiedijk
-/

namespace DiniTheoremOQ01OQ02

open Set Filter Topology

-- ============================================================
-- Part I: The supremum of xⁿ over [0,1) is exactly 1
-- ============================================================

/-- **The least upper bound of `{ xⁿ : x ∈ [0,1) }` is `1`** (for `n ≥ 1`).

    Upper bound: every `x ∈ [0,1)` has `xⁿ ≤ 1`.  Least: any upper bound `b` satisfies
    `1 ≤ b`, because the points `xₖ = 1 − 1/(k+1) ∈ [0,1)` give `xₖⁿ → 1`, and each
    `xₖⁿ ≤ b`, so the limit `1 ≤ b`.  The supremum is therefore `1`, even though it is
    never attained (`xⁿ < 1` for all `x ∈ [0,1)`). -/
theorem pow_image_Ico_isLUB (n : ℕ) (hn : 1 ≤ n) :
    IsLUB ((fun x : ℝ => x ^ n) '' Ico (0 : ℝ) 1) 1 := by
  constructor
  · -- `1` is an upper bound: `xⁿ ≤ 1` on `[0,1)`.
    rintro y ⟨x, hx, rfl⟩
    exact pow_le_one₀ hx.1 (le_of_lt hx.2)
  · -- `1` is the least upper bound: any upper bound `b` has `1 ≤ b`.
    intro b hb
    -- `xₖ = 1 − 1/(k+1) → 1`, hence `xₖⁿ → 1`.
    have hzero : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hbase : Tendsto (fun k : ℕ => (1 : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hzero)
    have hseq : Tendsto (fun k : ℕ => ((1 : ℝ) - 1 / ((k : ℝ) + 1)) ^ n) atTop (𝓝 1) := by
      simpa using hbase.pow n
    refine le_of_tendsto' hseq ?_
    intro k
    -- each `xₖⁿ` is in the image, so is `≤ b`.
    apply hb
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    refine ⟨1 - 1 / ((k : ℝ) + 1), ⟨?_, ?_⟩, rfl⟩
    · -- `0 ≤ xₖ`
      rw [sub_nonneg, div_le_one hk]
      have := Nat.cast_nonneg (α := ℝ) k; linarith
    · -- `xₖ < 1`
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith

/-- The set `{ xⁿ : x ∈ [0,1) }` is nonempty (contains `0ⁿ = 0`, as `n ≥ 1`). -/
theorem pow_image_Ico_nonempty (n : ℕ) :
    ((fun x : ℝ => x ^ n) '' Ico (0 : ℝ) 1).Nonempty :=
  ⟨(0 : ℝ) ^ n, 0, ⟨le_refl 0, zero_lt_one⟩, rfl⟩

/-- **The supremum of `xⁿ` over `[0,1)` equals `1`** (for `n ≥ 1`). -/
theorem pow_sSup_Ico (n : ℕ) (hn : 1 ≤ n) :
    sSup ((fun x : ℝ => x ^ n) '' Ico (0 : ℝ) 1) = 1 :=
  (pow_image_Ico_isLUB n hn).csSup_eq (pow_image_Ico_nonempty n)

-- ============================================================
-- Part II: The sharp modulus of non-uniform convergence
-- ============================================================

/-- **The sharp modulus is `1`.**  For every `n ≥ 1`, the uniform error of `xⁿ` against its
    pointwise limit `0` on `[0,1)`,

        sup_{x ∈ [0,1)} |xⁿ − 0|,

    equals exactly `1` — the sharp refinement of the parent's lower bound `1/2`.

    On `[0,1)` the error `|xⁿ − 0| = xⁿ` (it is nonnegative), so the error-image coincides
    with `{ xⁿ : x ∈ [0,1) }`, whose supremum is `1` by `pow_sSup_Ico`. -/
theorem pow_uniform_error_Ico (n : ℕ) (hn : 1 ≤ n) :
    sSup ((fun x : ℝ => |x ^ n - 0|) '' Ico (0 : ℝ) 1) = 1 := by
  have himg : (fun x : ℝ => |x ^ n - 0|) '' Ico (0 : ℝ) 1
      = (fun x : ℝ => x ^ n) '' Ico (0 : ℝ) 1 := by
    apply Set.image_congr
    intro x hx
    rw [sub_zero, abs_of_nonneg (pow_nonneg hx.1 n)]
  rw [himg]
  exact pow_sSup_Ico n hn

/-- **The LUB, unpacked.**  Since `1` is the *least* upper bound, no `c < 1` is an upper
    bound: for any `c < 1` and `n ≥ 1` there is a point of `[0,1)` with `xⁿ > c`. -/
theorem pow_exists_gt_of_lt_one (n : ℕ) (hn : 1 ≤ n) {c : ℝ} (hc : c < 1) :
    ∃ x ∈ Ico (0 : ℝ) 1, c < x ^ n := by
  by_contra h
  push_neg at h
  -- `c` would be an upper bound of the image, forcing `1 ≤ c`, contradicting `c < 1`.
  have hub : c ∈ upperBounds ((fun x : ℝ => x ^ n) '' Ico (0 : ℝ) 1) := by
    rintro y ⟨x, hx, rfl⟩
    exact h x hx
  have : (1 : ℝ) ≤ c := (pow_image_Ico_isLUB n hn).2 hub
  linarith

/-- **Sharpened non-uniformity.**  The convergence `xⁿ → 0` on `[0,1)` fails to be uniform
    with **any** threshold `c ∈ (0,1)` — not merely the parent's `1/2`.  Concretely, for
    every `c ∈ (0,1)` and every `N`, there is `n ≥ N` and a point `x ∈ [0,1)` whose error
    `|xⁿ − 0|` exceeds `c`.  Taking `c ↑ 1` recovers the sharp modulus. -/
theorem pow_not_tendstoUniformlyOn_Ico_sharp {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ TendstoUniformlyOn (fun n (x : ℝ) => x ^ n) (fun _ => (0 : ℝ)) atTop (Ico (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  push_neg
  refine ⟨c, hc0, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  refine ⟨N + 1, le_self_add, ?_⟩
  obtain ⟨x, hx, hxc⟩ := pow_exists_gt_of_lt_one (N + 1) (Nat.le_add_left 1 N) hc1
  refine ⟨x, hx, ?_⟩
  have hx0 : (0 : ℝ) ≤ x ^ (N + 1) := pow_nonneg hx.1 _
  show c ≤ dist (0 : ℝ) (x ^ (N + 1))
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hx0]
  linarith [hxc]

#check @pow_image_Ico_isLUB
#check @pow_sSup_Ico
#check @pow_uniform_error_Ico
#check @pow_not_tendstoUniformlyOn_Ico_sharp

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `pow_image_Ico_isLUB` / `pow_sSup_Ico` — `sup_{x∈[0,1)} xⁿ = 1` (LUB, never attained).
* `pow_uniform_error_Ico` — the sharp modulus: `sup_{x∈[0,1)} |xⁿ − 0| = 1` for all `n ≥ 1`.
* `pow_exists_gt_of_lt_one` — for any `c < 1`, some `x ∈ [0,1)` has `xⁿ > c`.
* `pow_not_tendstoUniformlyOn_Ico_sharp` — non-uniformity with any threshold `c ∈ (0,1)`.

This answers `dini-theorem-oq-01-oq-02`: the modulus of non-uniform convergence of `xⁿ` on
`[0,1)` is exactly `1`, sharpening the parent's `1/2`.  The supremum is approached along
`x = 1 − 1/(k+1) → 1` but never attained, which is precisely why Dini's compactness
hypothesis cannot be dropped on `[0,1)`.
-/

end DiniTheoremOQ01OQ02
