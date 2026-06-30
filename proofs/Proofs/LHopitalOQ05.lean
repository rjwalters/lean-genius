import Mathlib

/-
# The Cubic Sine Limit (OQ-05)

    lim_{x → 0} (x - sin x) / x³ = 1/6.

This is the classic third-order L'Hôpital / Taylor limit: numerator and
denominator both vanish to third order at `0`, and the leading nonzero Taylor
term of `x - sin x` is `x³/6`, so the ratio tends to `1/6`.

Rather than apply L'Hôpital's rule three times, we use the explicit cubic Taylor
bound for sine that already lives in Mathlib,

    Real.sin_bound : |x| ≤ 1 → |sin x - (x - x³/6)| ≤ |x|⁴ · (5/96).

The error term has degree `4` while we divide by `x³`, so the deviation of
`(x - sin x)/x³` from `1/6` is controlled *linearly* in `x`:

    |(x - sin x)/x³ - 1/6| = |sin x - (x - x³/6)| / |x|³ ≤ (5/96)·|x|.

This bound holds for every `0 < |x| ≤ 1`, and `(5/96)·|x| → 0`, so a squeeze
delivers the limit. The hypothesis `|x| ≤ 1` is automatically met on a punctured
neighbourhood of `0`.

Self-contained: imports only Mathlib.
-/

namespace LHopitalOQ05

open Filter Topology

/-- **Linear deviation bound.** For `0 < |x| ≤ 1`, the difference quotient
`(x - sin x)/x³` differs from `1/6` by at most `(5/96)·|x|`. This is exactly the
cubic Taylor bound `Real.sin_bound`, divided through by `|x|³`. -/
theorem abs_sub_le (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |(x - Real.sin x) / x ^ 3 - 1 / 6| ≤ 5 / 96 * |x| := by
  have hb : (0 : ℝ) < |x| := abs_pos.mpr hx0
  -- Recast the deviation as `-(sin x - (x - x³/6)) / x³`.
  have heq : (x - Real.sin x) / x ^ 3 - 1 / 6
      = -(Real.sin x - (x - x ^ 3 / 6)) / x ^ 3 := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_pow, div_le_iff₀ (pow_pos hb 3)]
  calc |Real.sin x - (x - x ^ 3 / 6)|
      ≤ |x| ^ 4 * (5 / 96) := Real.sin_bound hx1
    _ = 5 / 96 * |x| * |x| ^ 3 := by ring

/-- **The cubic sine limit.** `(x - sin x)/x³ → 1/6` as `x → 0` through nonzero
`x`. Proved by squeezing the deviation `(x - sin x)/x³ - 1/6` between `0` and the
linear bound `(5/96)·|x|` of `abs_sub_le`. -/
theorem tendsto_cubic_sine :
    Tendsto (fun x => (x - Real.sin x) / x ^ 3) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 6)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun x => 5 / 96 * |x|)
  · -- eventual bound: holds wherever `x ≠ 0` and `|x| ≤ 1`
    have hmem : Metric.closedBall (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 one_pos)
    filter_upwards [self_mem_nhdsWithin, hmem] with x hx hxball
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxball
    rw [Real.norm_eq_abs]
    exact abs_sub_le x hx hxball
  · -- the bound tends to `0`
    have habs : Tendsto (fun x : ℝ => |x|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    have h0 : Tendsto (fun x : ℝ => 5 / 96 * |x|) (𝓝[≠] (0 : ℝ)) (𝓝 (5 / 96 * 0)) :=
      (habs.mono_left nhdsWithin_le_nhds).const_mul (5 / 96)
    simpa using h0

/-- The limit value `1/6` is exactly the reciprocal of `3! = 6`, i.e. the third
Taylor coefficient of `x - sin x`. This packaging makes explicit that the cubic
sine limit is the order-3 Taylor statement. -/
theorem tendsto_cubic_sine_factorial :
    Tendsto (fun x => (x - Real.sin x) / x ^ 3) (𝓝[≠] (0 : ℝ))
      (𝓝 (1 / (Nat.factorial 3 : ℝ))) := by
  have h := tendsto_cubic_sine
  norm_num [Nat.factorial] at h ⊢
  exact h

#check @tendsto_cubic_sine

end LHopitalOQ05
