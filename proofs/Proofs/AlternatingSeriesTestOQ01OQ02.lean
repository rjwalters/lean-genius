import Mathlib

/-
# Abel-Summation Error Bounds for Alternating Series with Bounded-Variation Coefficients

The classical alternating series test (Leibniz) and its sharp two-sided refinement
(`AlternatingSeriesTestOQ01`, `AlternatingSeriesTestOQ01OQ01`) bound the truncation error
of `S_N = ∑_{i<N} (-1)^i a_i` **only when the coefficients `a` are antitone**. The first
omitted term `a N` then controls the error: `|S_N - l| ≤ a N`.

This file removes the monotonicity hypothesis entirely. Via **summation by parts**
(Abel's transformation, `Finset.sum_range_by_parts`) we prove a Cauchy-difference estimate
valid for an **arbitrary** real coefficient sequence:

`|S_M - S_N| ≤ |a (M-1)| + ∑_{i ∈ [N, M-1)} |a (i+1) - a i|`     (for `N < M`).

The right-hand side is a **boundary term plus the total variation of `a` on `[N, M-1)`**.
This is the quantitative core of the **Dirichlet test**: the partial sums of the sign
sequence `(-1)^i` are bounded by `1` (they are `0` or `1`, `neg_one_geom_sum`), so Abel
summation trades the (possibly non-monotone) oscillation of `a` for its total variation.

Two consequences are recorded:

* `abs_partialSum_diff_le_of_antitone` — for antitone `a ≥ 0` the variation telescopes and
  the boundary term cancels, collapsing the bound back to the Leibniz value `a N`. The new
  estimate therefore *contains* the classical one as the monotone special case.

* `abs_partialSum_sub_limit_le_tail_variation` — passing `M → ∞` for a convergent series
  bounds the genuine limit error `|S_N - l|` by a controlling tail value `V`. With non-
  monotone coefficients the tail total variation plays the role of the Leibniz remainder.

All results are over `ℝ`. No monotonicity is assumed anywhere except in the antitone
corollary. The bounded-variation error bound is absent from Mathlib.
-/

namespace AlternatingSeriesTestOQ01OQ02

open Finset Filter Topology

variable {a : ℕ → ℝ} {l : ℝ}

/-- The partial sums of the sign sequence `(-1)^i` are bounded by `1`: they equal `0` (for
even length) or `1` (for odd length), by `neg_one_geom_sum`. This is the boundedness
hypothesis that powers the Dirichlet test. -/
theorem abs_signSum_le (n : ℕ) : |∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ 1 := by
  rw [neg_one_geom_sum]
  split <;> simp

/-- Elementary triangle bound `|x - y| ≤ |x| + |y|`. -/
private theorem abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])

/-- **Abel-summation (Dirichlet) error bound for arbitrary coefficients.** For any real
sequence `a` and any `N < M`, the alternating block sum `∑_{i ∈ [N,M)} (-1)^i a i` is
controlled by a boundary term plus the total variation of `a` on `[N, M-1)`:

`|∑_{i ∈ [N,M)} (-1)^i a i| ≤ |a (M-1)| + ∑_{i ∈ [N,M-1)} |a (i+1) - a i|`.

No monotonicity of `a` is required; this is the mechanism of the Dirichlet test made
quantitative. -/
theorem abs_alternating_Ico_le (a : ℕ → ℝ) {N M : ℕ} (hNM : N < M) :
    |∑ i ∈ Ico N M, (-1 : ℝ) ^ i * a i|
      ≤ |a (M - 1)| + ∑ i ∈ Ico N (M - 1), |a (i + 1) - a i| := by
  set n := M - N with hn
  have hn1 : 1 ≤ n := by omega
  -- Reindex `[N,M)` to `range n` and factor out the constant sign `(-1)^N`.
  have hreindex :
      ∑ i ∈ Ico N M, (-1 : ℝ) ^ i * a i
        = (-1 : ℝ) ^ N * ∑ j ∈ range n, (-1 : ℝ) ^ j * a (N + j) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]; ring
  -- Summation by parts on the reindexed (sign × coefficient) sum.
  have hbp :
      ∑ j ∈ range n, (-1 : ℝ) ^ j * a (N + j)
        = a (N + (n - 1)) * (∑ i ∈ range n, (-1 : ℝ) ^ i)
          - ∑ j ∈ range (n - 1),
              (a (N + (j + 1)) - a (N + j)) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i) := by
    have h := Finset.sum_range_by_parts (fun j => a (N + j)) (fun j => (-1 : ℝ) ^ j) n
    simp only [smul_eq_mul] at h
    rw [show (∑ j ∈ range n, a (N + j) * (-1 : ℝ) ^ j)
          = ∑ j ∈ range n, (-1 : ℝ) ^ j * a (N + j) from
        Finset.sum_congr rfl fun j _ => by ring] at h
    exact h
  have hsign : |(-1 : ℝ) ^ N| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [hreindex, abs_mul, hsign, one_mul, hbp]
  -- Triangle inequality, then bound each sign partial sum by `1`.
  have hbnd :
      |a (N + (n - 1)) * (∑ i ∈ range n, (-1 : ℝ) ^ i)
          - ∑ j ∈ range (n - 1),
              (a (N + (j + 1)) - a (N + j)) * (∑ i ∈ range (j + 1), (-1 : ℝ) ^ i)|
        ≤ |a (N + (n - 1))|
          + ∑ j ∈ range (n - 1), |a (N + (j + 1)) - a (N + j)| := by
    refine (abs_sub_le_add _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_signSum_le n)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_signSum_le _)
  have hidx : N + (n - 1) = M - 1 := by rw [hn]; omega
  refine hbnd.trans (le_of_eq ?_)
  congr 1
  · rw [hidx]
  · rw [Finset.sum_Ico_eq_sum_range, show M - 1 - N = n - 1 from by omega]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show N + j + 1 = N + (j + 1) from by omega]

/-- The block sum `∑_{i ∈ [N,M)} (-1)^i a i` equals the difference of partial sums
`S_M - S_N`, where `S_k = ∑_{i<k} (-1)^i a i`. -/
theorem partialSum_diff_eq (a : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ i ∈ range M, (-1 : ℝ) ^ i * a i) - (∑ i ∈ range N, (-1 : ℝ) ^ i * a i)
      = ∑ i ∈ Ico N M, (-1 : ℝ) ^ i * a i :=
  (Finset.sum_Ico_eq_sub _ hNM).symm

/-- **Cauchy-difference Abel bound, partial-sum form.** The truncation error between two
partial sums is bounded by the last coefficient plus the total variation in between:

`|S_M - S_N| ≤ |a (M-1)| + ∑_{i ∈ [N,M-1)} |a (i+1) - a i|`. -/
theorem abs_partialSum_diff_le (a : ℕ → ℝ) {N M : ℕ} (hNM : N < M) :
    |(∑ i ∈ range M, (-1 : ℝ) ^ i * a i) - (∑ i ∈ range N, (-1 : ℝ) ^ i * a i)|
      ≤ |a (M - 1)| + ∑ i ∈ Ico N (M - 1), |a (i + 1) - a i| := by
  rw [partialSum_diff_eq a (le_of_lt hNM)]
  exact abs_alternating_Ico_le a hNM

/-- **Monotone special case recovers Leibniz.** For an antitone, nonnegative coefficient
sequence the total variation telescopes and the boundary term cancels, collapsing the Abel
bound to the classical first-omitted-term estimate `|S_M - S_N| ≤ a N`. -/
theorem abs_partialSum_diff_le_of_antitone (hmono : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    {N M : ℕ} (hNM : N < M) :
    |(∑ i ∈ range M, (-1 : ℝ) ^ i * a i) - (∑ i ∈ range N, (-1 : ℝ) ^ i * a i)| ≤ a N := by
  refine (abs_partialSum_diff_le a hNM).trans ?_
  have hvar : ∑ i ∈ Ico N (M - 1), |a (i + 1) - a i| = a N - a (M - 1) := by
    -- antitone ⇒ each `|a (i+1) - a i| = a i - a (i+1)`, telescoping over `[N, M-1)`.
    have hpoint : ∀ i ∈ Ico N (M - 1), |a (i + 1) - a i| = a i - a (i + 1) := by
      intro i _
      rw [abs_of_nonpos (by linarith [hmono (Nat.le_succ i)])]; ring
    rw [Finset.sum_congr rfl hpoint, Finset.sum_Ico_eq_sum_range,
      show M - 1 - N = M - 1 - N from rfl]
    have htel : ∑ j ∈ range (M - 1 - N), (a (N + j) - a (N + (j + 1)))
        = a (N + 0) - a (N + (M - 1 - N)) := Finset.sum_range_sub' (fun j => a (N + j)) _
    rw [show (∑ j ∈ range (M - 1 - N), (a (N + j) - a (N + j + 1)))
          = ∑ j ∈ range (M - 1 - N), (a (N + j) - a (N + (j + 1))) from
        Finset.sum_congr rfl fun j _ => by rw [show N + j + 1 = N + (j + 1) from by omega]]
    rw [htel, Nat.add_zero, show N + (M - 1 - N) = M - 1 from by omega]
  rw [hvar]
  have hle : a (M - 1) ≤ a N := hmono (by omega)
  linarith [abs_of_nonneg (hpos (M - 1))]

/-- **Bounded-variation remainder bound at the limit.** If the alternating series converges
to `l` and the boundary-plus-variation quantity is `≤ V` for arbitrarily large truncation
points `M`, then the genuine truncation error obeys the same bound:

`|S_N - l| ≤ V`.

This is the bounded-variation analogue of the Leibniz remainder `|S_N - l| ≤ a N`: it holds
for non-monotone coefficients, with the controlling value `V` (typically the infinite tail
total variation) playing the role of `a N`. -/
theorem abs_partialSum_sub_limit_le_tail_variation
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * a i) atTop (𝓝 l))
    (N : ℕ) {V : ℝ}
    (hV : ∀ᶠ M in atTop, |a (M - 1)| + ∑ i ∈ Ico N (M - 1), |a (i + 1) - a i| ≤ V) :
    |(∑ i ∈ range N, (-1 : ℝ) ^ i * a i) - l| ≤ V := by
  have hcont : Tendsto (fun M => |(∑ i ∈ range N, (-1 : ℝ) ^ i * a i)
      - (∑ i ∈ range M, (-1 : ℝ) ^ i * a i)|) atTop
      (𝓝 |(∑ i ∈ range N, (-1 : ℝ) ^ i * a i) - l|) :=
    (Filter.Tendsto.const_sub _ hl).abs
  refine le_of_tendsto hcont ?_
  filter_upwards [eventually_gt_atTop N, hV] with M hM hMV
  have hbound := abs_partialSum_diff_le a hM
  rw [abs_sub_comm] at hbound
  exact hbound.trans hMV

end AlternatingSeriesTestOQ01OQ02
