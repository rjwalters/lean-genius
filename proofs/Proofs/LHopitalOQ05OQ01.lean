import Mathlib

/-
# The Companion Cosine Limit (OQ-05 / OQ-01)

    lim_{x → 0} (1 - cos x) / x² = 1/2.

This is the even-order companion of the cubic sine limit `(x - sin x)/x³ → 1/6`
(`LHopitalOQ05`). Numerator and denominator both vanish to second order at `0`,
and the leading nonzero Taylor term of `1 - cos x` is `x²/2`, so the ratio tends
to `1/2`.

Rather than apply L'Hôpital's rule twice, we use the explicit quadratic Taylor
bound for cosine that already lives in Mathlib,

    Real.cos_bound : |x| ≤ 1 → |cos x - (1 - x²/2)| ≤ |x|⁴ · (5/96).

The error term has degree `4` while we divide by `x²`, so the deviation of
`(1 - cos x)/x²` from `1/2` is controlled *quadratically* in `x`:

    |(1 - cos x)/x² - 1/2| = |cos x - (1 - x²/2)| / |x|² ≤ (5/96)·|x|².

This bound holds for every `0 < |x| ≤ 1`, and `(5/96)·|x|² → 0`, so a squeeze
delivers the limit. The hypothesis `|x| ≤ 1` is automatically met on a punctured
neighbourhood of `0`.

This mirrors the cubic sine proof exactly, with `Real.cos_bound` in place of
`Real.sin_bound` and one fewer power of `x` divided out.

Self-contained: imports only Mathlib.
-/

namespace LHopitalOQ05OQ01

open Filter Topology

/-- **Quadratic deviation bound.** For `0 < |x| ≤ 1`, the difference quotient
`(1 - cos x)/x²` differs from `1/2` by at most `(5/96)·|x|²`. This is exactly the
quadratic Taylor bound `Real.cos_bound`, divided through by `|x|²`. -/
theorem abs_sub_le (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |(1 - Real.cos x) / x ^ 2 - 1 / 2| ≤ 5 / 96 * |x| ^ 2 := by
  have hb : (0 : ℝ) < |x| := abs_pos.mpr hx0
  -- Recast the deviation as `-(cos x - (1 - x²/2)) / x²`.
  have heq : (1 - Real.cos x) / x ^ 2 - 1 / 2
      = -(Real.cos x - (1 - x ^ 2 / 2)) / x ^ 2 := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_pow, div_le_iff₀ (pow_pos hb 2)]
  calc |Real.cos x - (1 - x ^ 2 / 2)|
      ≤ |x| ^ 4 * (5 / 96) := Real.cos_bound hx1
    _ = 5 / 96 * |x| ^ 2 * |x| ^ 2 := by ring

/-- **The companion cosine limit.** `(1 - cos x)/x² → 1/2` as `x → 0` through
nonzero `x`. Proved by squeezing the deviation `(1 - cos x)/x² - 1/2` between `0`
and the quadratic bound `(5/96)·|x|²` of `abs_sub_le`. -/
theorem tendsto_cosine_quadratic :
    Tendsto (fun x => (1 - Real.cos x) / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun x => 5 / 96 * |x| ^ 2)
  · -- eventual bound: holds wherever `x ≠ 0` and `|x| ≤ 1`
    have hmem : Metric.closedBall (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 one_pos)
    filter_upwards [self_mem_nhdsWithin, hmem] with x hx hxball
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxball
    rw [Real.norm_eq_abs]
    exact abs_sub_le x hx hxball
  · -- the bound tends to `0`
    have habs : Tendsto (fun x : ℝ => |x| ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).pow 2
    have h0 : Tendsto (fun x : ℝ => 5 / 96 * |x| ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (5 / 96 * 0)) :=
      (habs.mono_left nhdsWithin_le_nhds).const_mul (5 / 96)
    simpa using h0

/-- The limit value `1/2` is exactly the reciprocal of `2! = 2`, i.e. the second
Taylor coefficient of `1 - cos x`. This packaging makes explicit that the
companion cosine limit is the order-2 Taylor statement. -/
theorem tendsto_cosine_quadratic_factorial :
    Tendsto (fun x => (1 - Real.cos x) / x ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (1 / (Nat.factorial 2 : ℝ))) := by
  have h := tendsto_cosine_quadratic
  norm_num [Nat.factorial] at h ⊢
  exact h

#check @tendsto_cosine_quadratic

end LHopitalOQ05OQ01
