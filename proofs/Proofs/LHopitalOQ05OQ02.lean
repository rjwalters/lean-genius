import Mathlib

/-
# A General Remainder-Bound Limit Lemma, Generalising abs_sub_le Beyond Sine (OQ-05-OQ-02)

This answers the parent L'Hôpital entry's OQ-05-OQ-02, which asks for a general
order-`n` version of the parent's cubic-sine argument: a single lemma that, *from
an explicit Taylor remainder bound alone*, produces the indeterminate limit
`(f(x) − T_{n−1}(x))/xⁿ → f^{(n)}(0)/n!` — generalising the parent's sine-specific
deviation lemma `abs_sub_le` to arbitrary order and arbitrary functions.

## The general engine

The headline `tendsto_of_remainder_bound` abstracts the parent's argument away
from sine entirely.  Suppose a difference quotient `g` deviates from a target
value `L` by exactly `−e(x)/xⁿ`, where `e` is the function's deviation from its
Taylor polynomial, and one has an explicit higher-degree remainder bound
`|e(x)| ≤ C·|x|^m` with `n < m` valid for `|x| ≤ 1`.  Then `g x → L`.  The proof
divides the bound by `|x|ⁿ` and uses `|x|^m ≤ |x|^{n+1}` on the unit ball to leave
the linear envelope `C·|x|`, which a squeeze sends to `0`.  Only the explicit
remainder bound is consumed — no differentiation, no L'Hôpital, no Mean Value
Theorem — so the lemma applies to any `f` whose Taylor remainder Mathlib bounds.

## Two instances (and the value `L = f^{(n)}(0)/n!`)

  • cosine: `e(x) = cos x − (1 − x²/2)`,  `n = 2, m = 4, L = 1/2 = 1/2!`  (`Real.cos_bound`)
  • sine:   `e(x) = sin x − (x − x³/6)`,  `n = 3, m = 4, L = 1/6 = 1/3!`  (`Real.sin_bound`)

Both limits drop out of the one lemma with only the parameters `(e, n, m, C, L)`
changing, and in each the target `L` is exactly the leading Taylor coefficient
`f^{(n)}(0)/n!` (recorded by the `…_factorial` packagings) — the order-`n` reading
OQ-02 requests.  The remaining abstraction (auto-deriving the deviation identity
from a formal Taylor polynomial, rather than supplying it per instance) is left as
an open question.

Self-contained: imports only Mathlib.
-/

namespace LHopitalOQ05OQ02

open Filter Topology

/-- **Unified second-order remainder squeeze.**  Suppose a difference quotient
`g` deviates from a target value `L` by exactly `−e(x)/xⁿ` on the punctured
neighbourhood of `0`, and the remainder `e` obeys an explicit higher-degree
bound `|e(x)| ≤ C·|x|^m` with `n < m` for `|x| ≤ 1`.  Then `g x → L` as `x → 0`.

This is the common engine behind every "`f(x)/xⁿ` tends to the `n`-th Taylor
coefficient" limit whose remainder Mathlib bounds explicitly; the quadratic
cosine limit and the cubic sine limit below are two instances. -/
theorem tendsto_of_remainder_bound
    (g e : ℝ → ℝ) (L C : ℝ) (n m : ℕ)
    (hC : 0 ≤ C) (hnm : n + 1 ≤ m)
    (hdev : ∀ x : ℝ, x ≠ 0 → g x - L = -(e x) / x ^ n)
    (hbound : ∀ x : ℝ, |x| ≤ 1 → |e x| ≤ C * |x| ^ m) :
    Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 L) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun x => C * |x|)
  · -- eventual deviation bound on the punctured closed unit ball
    have hmem : Metric.closedBall (0 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 one_pos)
    filter_upwards [self_mem_nhdsWithin, hmem] with x hx hxball
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxball
    have hb : (0 : ℝ) < |x| := abs_pos.mpr hx
    rw [Real.norm_eq_abs, hdev x hx, abs_div, abs_neg, abs_pow,
      div_le_iff₀ (pow_pos hb n)]
    -- goal: `|e x| ≤ C * |x| * |x| ^ n`
    have hpow : |x| ^ m ≤ |x| ^ (n + 1) :=
      pow_le_pow_of_le_one (abs_nonneg x) hxball hnm
    calc |e x| ≤ C * |x| ^ m := hbound x hxball
      _ ≤ C * |x| ^ (n + 1) := mul_le_mul_of_nonneg_left hpow hC
      _ = C * |x| * |x| ^ n := by rw [pow_succ]; ring
  · -- the linear bound tends to `0`
    have habs : Tendsto (fun x : ℝ => |x|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    have h0 : Tendsto (fun x : ℝ => C * |x|) (𝓝[≠] (0 : ℝ)) (𝓝 (C * 0)) :=
      (habs.mono_left nhdsWithin_le_nhds).const_mul C
    simpa using h0

/-- **Quadratic cosine deviation bound.**  For `0 < |x| ≤ 1`, the quotient
`(1 − cos x)/x²` differs from `1/2` by at most `(5/96)·|x|²`.  This is
`Real.cos_bound` divided through by `|x|²`: the remainder has degree `4` while
the denominator is `x²`, so the deviation is controlled *quadratically* in `x`. -/
theorem abs_sub_le_cos (x : ℝ) (hx0 : x ≠ 0) (hx1 : |x| ≤ 1) :
    |(1 - Real.cos x) / x ^ 2 - 1 / 2| ≤ 5 / 96 * |x| ^ 2 := by
  have hb : (0 : ℝ) < |x| := abs_pos.mpr hx0
  have heq : (1 - Real.cos x) / x ^ 2 - 1 / 2
      = -(Real.cos x - (1 - x ^ 2 / 2)) / x ^ 2 := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_pow, div_le_iff₀ (pow_pos hb 2)]
  calc |Real.cos x - (1 - x ^ 2 / 2)|
      ≤ |x| ^ 4 * (5 / 96) := Real.cos_bound hx1
    _ = 5 / 96 * |x| ^ 2 * |x| ^ 2 := by ring

/-- **The companion cosine limit.**  `(1 − cos x)/x² → 1/2` as `x → 0` through
nonzero `x`.  Obtained directly from the unified `tendsto_of_remainder_bound`
with remainder `e(x) = cos x − (1 − x²/2)`, denominator degree `n = 2`, and the
Mathlib bound `Real.cos_bound` (degree `m = 4`). -/
theorem tendsto_cosine_quadratic :
    Tendsto (fun x => (1 - Real.cos x) / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
  refine tendsto_of_remainder_bound
    (fun x => (1 - Real.cos x) / x ^ 2)
    (fun x => Real.cos x - (1 - x ^ 2 / 2))
    (1 / 2) (5 / 96) 2 4 (by norm_num) (by norm_num) ?_ ?_
  · intro x hx
    field_simp
    ring
  · intro x hx
    linarith [Real.cos_bound hx]

/-- The limit value `1/2` is exactly the reciprocal of `2! = 2`, i.e. the second
Taylor coefficient of `1 − cos`.  This packaging makes explicit that the
quadratic cosine limit is the order-`2` Taylor statement, mirroring the parent's
`tendsto_cubic_sine_factorial`. -/
theorem tendsto_cosine_factorial :
    Tendsto (fun x => (1 - Real.cos x) / x ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (1 / (Nat.factorial 2 : ℝ))) := by
  have h := tendsto_cosine_quadratic
  norm_num [Nat.factorial] at h ⊢
  exact h

/-- **The cubic sine limit, re-derived through the unified lemma.**  This is the
parent OQ-05 result `(x − sin x)/x³ → 1/6`, now obtained as a *second* instance
of `tendsto_of_remainder_bound` (remainder `e(x) = sin x − (x − x³/6)`,
denominator degree `n = 3`, Mathlib bound `Real.sin_bound` of degree `m = 4`).
Proving the parent's result and the new cosine result by the same lemma is the
"single second-order remainder statement" requested by OQ-05-OQ-01. -/
theorem tendsto_cubic_sine_unified :
    Tendsto (fun x => (x - Real.sin x) / x ^ 3) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 6)) := by
  refine tendsto_of_remainder_bound
    (fun x => (x - Real.sin x) / x ^ 3)
    (fun x => Real.sin x - (x - x ^ 3 / 6))
    (1 / 6) (5 / 96) 3 4 (by norm_num) (by norm_num) ?_ ?_
  · intro x hx
    field_simp
    ring
  · intro x hx
    linarith [Real.sin_bound hx]

#check @tendsto_of_remainder_bound
#check @tendsto_cosine_quadratic

end LHopitalOQ05OQ02
