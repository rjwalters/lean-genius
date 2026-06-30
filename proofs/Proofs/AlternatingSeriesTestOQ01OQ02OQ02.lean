import Mathlib

/-
# The Quantitative Abstract Dirichlet Test: Total-Variation Error Bounds for Arbitrary Factor Sequences

The parent file `AlternatingSeriesTestOQ01OQ02` proves, via summation by parts, a
total-variation error bound for the **sign-weighted** block sum
`∑_{i∈[N,M)} (-1)^i a i` of an arbitrary (non-monotone) real coefficient sequence:

`|∑_{i∈[N,M)} (-1)^i a i| ≤ |a (M-1)| + ∑_{i∈[N,M-1)} |a (i+1) - a i|`.

The sibling `AlternatingSeriesTestOQ01OQ02OQ01` sharpens this to a two-sided
Jordan-decomposition trap. **Both are specialized to the single factor sequence `(-1)^i`.**

This file removes that specialization. The actual mechanism of Abel summation cares only
that the factor sequence `b` has **bounded partial sums**; the value `(-1)^i` is irrelevant.
We prove the *abstract Dirichlet test in quantitative form*: for any real factor sequence
`b` whose partial sums obey `|∑_{i<k} b i| ≤ B`, and any real coefficient sequence `a`,

`|∑_{j<n} b j · a j| ≤ B·|a (n-1)| + B·∑_{j<n-1} |a (j+1) - a j|`                 (`abs_dirichlet_range_le`)

and, over an arbitrary window `[N,M)` (where the relevant shifted partial sums are bounded
by `2B`),

`|∑_{j∈[N,M)} b j · a j| ≤ 2B·|a (M-1)| + 2B·∑_{j∈[N,M-1)} |a (j+1) - a j|`.       (`abs_dirichlet_Ico_le`)

Three consequences are recorded:

* `abs_alternating_range_le` — taking `b = (-1)^i` and `B = 1` recovers the parent's bound
  (range form). The abstract estimate therefore *contains* the classical alternating one as
  the special case of the sign factor.

* `abs_dirichlet_diff_le_of_antitone` — for an antitone, nonnegative coefficient sequence
  the boundary term and the total variation combine and collapse the window bound to the
  clean **quantitative Dirichlet remainder** `|S_M - S_N| ≤ 2B·a N`, where
  `S_k = ∑_{i<k} b i · a i`.

* `abs_dirichlet_sub_limit_le` — passing `M → ∞` for a convergent Dirichlet series bounds
  the genuine truncation error `|S_N - l| ≤ 2B·a N`.

The contrast with Mathlib is the point. Mathlib's `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`
proves Dirichlet's test **qualitatively** (the partial sums are Cauchy, hence converge) and
requires monotonicity of `a` throughout. It gives **no rate**. The bounds here are
quantitative: an explicit total-variation estimate valid for *non-monotone* `a`, and an
explicit `2B·a N` remainder in the monotone case — neither is in Mathlib.

All results are over `ℝ` and build on `Finset.sum_range_by_parts`.
-/

namespace AlternatingSeriesTestOQ01OQ02OQ02

open Finset Filter Topology

/-- Elementary triangle bound `|x - y| ≤ |x| + |y|`. -/
private theorem abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])

/-- **Quantitative abstract Dirichlet test (range form).** For any real factor sequence `b`
whose partial sums are bounded by `B`, and any real coefficient sequence `a`, the weighted
sum `∑_{j<n} b j · a j` is controlled by a boundary term plus the total variation of `a`,
each scaled by `B`:

`|∑_{j<n} b j · a j| ≤ B·|a (n-1)| + B·∑_{j<n-1} |a (j+1) - a j|`.

No monotonicity of `a` and no special structure of `b` (beyond bounded partial sums) is
required. This is the engine of the Dirichlet test: Abel summation trades the oscillation of
the factor `b` for its uniform partial-sum bound `B`, leaving the total variation of `a`. -/
theorem abs_dirichlet_range_le (a b : ℕ → ℝ) {B : ℝ}
    (hB : ∀ k, |∑ i ∈ range k, b i| ≤ B) (n : ℕ) :
    |∑ j ∈ range n, b j * a j|
      ≤ B * |a (n - 1)| + B * ∑ j ∈ range (n - 1), |a (j + 1) - a j| := by
  -- Summation by parts: peel off the boundary term and the increment sum.
  have hbp := Finset.sum_range_by_parts a b n
  simp only [smul_eq_mul] at hbp
  have hcomm : ∑ j ∈ range n, b j * a j = ∑ i ∈ range n, a i * b i :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hcomm, hbp]
  refine (abs_sub_le_add _ _).trans (add_le_add ?_ ?_)
  · -- boundary term: `|a(n-1) · ∑_{i<n} b i| ≤ B·|a(n-1)|`
    rw [abs_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB n) (abs_nonneg _)
  · -- increment sum: triangle inequality, then bound each factor partial sum by `B`
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)

/-- **Quantitative abstract Dirichlet test (window form).** Over an arbitrary window
`[N,M)`, the partial sums of the *shifted* factor sequence are bounded by `2B` (difference
of two `B`-bounded prefix sums), so the window weighted sum obeys

`|∑_{j∈[N,M)} b j · a j| ≤ 2B·|a (M-1)| + 2B·∑_{j∈[N,M-1)} |a (j+1) - a j|`. -/
theorem abs_dirichlet_Ico_le (a b : ℕ → ℝ) {B : ℝ}
    (hB : ∀ k, |∑ i ∈ range k, b i| ≤ B) {N M : ℕ} (hNM : N < M) :
    |∑ j ∈ Ico N M, b j * a j|
      ≤ 2 * B * |a (M - 1)| + 2 * B * ∑ j ∈ Ico N (M - 1), |a (j + 1) - a j| := by
  set n := M - N with hn
  have hn1 : 1 ≤ n := by omega
  -- Reindex the window `[N,M)` to `range n` via the shifted sequences `a(N+·)`, `b(N+·)`.
  have hreindex : ∑ j ∈ Ico N M, b j * a j
      = ∑ k ∈ range n, b (N + k) * a (N + k) := by
    rw [hn, Finset.sum_Ico_eq_sum_range]
  -- The shifted prefix sums are differences of two `B`-bounded prefix sums ⇒ bounded by `2B`.
  have hB' : ∀ k, |∑ i ∈ range k, (fun i => b (N + i)) i| ≤ 2 * B := by
    intro k
    show |∑ i ∈ range k, b (N + i)| ≤ 2 * B
    have hsplit : ∑ i ∈ range k, b (N + i)
        = (∑ i ∈ range (N + k), b i) - ∑ i ∈ range N, b i := by
      have h1 : ∑ i ∈ range k, b (N + i) = ∑ i ∈ Ico N (N + k), b i := by
        rw [Finset.sum_Ico_eq_sum_range]; simp
      rw [h1, eq_sub_iff_add_eq, add_comm,
        Finset.sum_range_add_sum_Ico b (Nat.le_add_right N k)]
    rw [hsplit]
    calc |(∑ i ∈ range (N + k), b i) - ∑ i ∈ range N, b i|
        ≤ |∑ i ∈ range (N + k), b i| + |∑ i ∈ range N, b i| := abs_sub_le_add _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring
  rw [hreindex]
  have hmain := abs_dirichlet_range_le (fun i => a (N + i)) (fun i => b (N + i)) hB' n
  refine hmain.trans (le_of_eq ?_)
  have hidx : N + (n - 1) = M - 1 := by omega
  have hsum : (∑ j ∈ range (n - 1), |a (N + (j + 1)) - a (N + j)|)
      = ∑ j ∈ Ico N (M - 1), |a (j + 1) - a j| := by
    rw [Finset.sum_Ico_eq_sum_range, show M - 1 - N = n - 1 from by omega]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show N + j + 1 = N + (j + 1) from by omega]
  rw [hidx, hsum]

/-- **Specialization to the sign factor recovers the classical bound.** Taking
`b = (-1)^i` (whose partial sums are bounded by `1`) collapses the abstract range bound to
the parent file's alternating-series estimate. -/
theorem abs_alternating_range_le (a : ℕ → ℝ) (n : ℕ) :
    |∑ j ∈ range n, (-1 : ℝ) ^ j * a j|
      ≤ |a (n - 1)| + ∑ j ∈ range (n - 1), |a (j + 1) - a j| := by
  have hsign : ∀ k, |∑ i ∈ range k, (-1 : ℝ) ^ i| ≤ 1 := by
    intro k; rw [neg_one_geom_sum]; split <;> simp
  have := abs_dirichlet_range_le a (fun i => (-1 : ℝ) ^ i) hsign n
  simpa using this

/-- **Quantitative Dirichlet remainder for monotone coefficients.** When `a` is antitone and
nonnegative the boundary term and the total variation telescope, collapsing the window bound
to the explicit rate `|S_M - S_N| ≤ 2B·a N`, where `S_k = ∑_{i<k} b i · a i`. This is the
quantitative content Mathlib's qualitative `cauchySeq_series_mul_of_tendsto_zero_of_bounded`
omits. -/
theorem abs_dirichlet_diff_le_of_antitone (a b : ℕ → ℝ) {B : ℝ}
    (hB : ∀ k, |∑ i ∈ range k, b i| ≤ B) (hmono : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    {N M : ℕ} (hNM : N < M) :
    |(∑ j ∈ range M, b j * a j) - ∑ j ∈ range N, b j * a j| ≤ 2 * B * a N := by
  rw [← Finset.sum_Ico_eq_sub _ (le_of_lt hNM)]
  refine (abs_dirichlet_Ico_le a b hB hNM).trans ?_
  -- The total variation of an antitone sequence telescopes.
  have hvar : ∑ j ∈ Ico N (M - 1), |a (j + 1) - a j| = a N - a (M - 1) := by
    have hpoint : ∀ j ∈ Ico N (M - 1), |a (j + 1) - a j| = a j - a (j + 1) := by
      intro j _
      rw [abs_of_nonpos (by linarith [hmono (Nat.le_succ j)])]; ring
    rw [Finset.sum_congr rfl hpoint, Finset.sum_Ico_eq_sum_range]
    have htel : ∑ j ∈ range (M - 1 - N), (a (N + j) - a (N + (j + 1)))
        = a (N + 0) - a (N + (M - 1 - N)) := Finset.sum_range_sub' (fun j => a (N + j)) _
    rw [show (∑ j ∈ range (M - 1 - N), (a (N + j) - a (N + j + 1)))
          = ∑ j ∈ range (M - 1 - N), (a (N + j) - a (N + (j + 1))) from
        Finset.sum_congr rfl fun j _ => by rw [show N + j + 1 = N + (j + 1) from by omega]]
    rw [htel, Nat.add_zero, show N + (M - 1 - N) = M - 1 from by omega]
  rw [hvar, abs_of_nonneg (hpos (M - 1))]
  have hkey : 2 * B * a (M - 1) + 2 * B * (a N - a (M - 1)) = 2 * B * a N := by ring
  linarith [hkey]

/-- **Quantitative Dirichlet remainder at the limit.** If the Dirichlet series
`S_n = ∑_{i<n} b i · a i` converges to `l` (with `a` antitone, nonnegative — exactly the
hypotheses under which Mathlib guarantees convergence when `a → 0`), then the truncation
error obeys the explicit bound `|S_N - l| ≤ 2B·a N`.

Mathlib proves convergence but supplies no rate; this is the rate. -/
theorem abs_dirichlet_sub_limit_le (a b : ℕ → ℝ) {B : ℝ} {l : ℝ}
    (hB : ∀ k, |∑ i ∈ range k, b i| ≤ B) (hmono : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    (hl : Tendsto (fun n => ∑ i ∈ range n, b i * a i) atTop (𝓝 l)) (N : ℕ) :
    |(∑ i ∈ range N, b i * a i) - l| ≤ 2 * B * a N := by
  have hcont : Tendsto (fun M => |(∑ i ∈ range N, b i * a i)
      - (∑ i ∈ range M, b i * a i)|) atTop
      (𝓝 |(∑ i ∈ range N, b i * a i) - l|) :=
    (Filter.Tendsto.const_sub _ hl).abs
  refine le_of_tendsto hcont ?_
  filter_upwards [eventually_gt_atTop N] with M hM
  have hbound := abs_dirichlet_diff_le_of_antitone a b hB hmono hpos hM
  rwa [abs_sub_comm] at hbound

end AlternatingSeriesTestOQ01OQ02OQ02
