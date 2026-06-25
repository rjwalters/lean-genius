import Mathlib

/-
# GCD Algorithm — OQ-05: The Gauss–Kuzmin Distribution is a Probability Distribution

## Research Problem: gcd-algorithm-oq-05

The Euclidean algorithm on `r₀, r₁` produces the quotient sequence
`qᵢ = ⌊r_{i-1}/rᵢ⌋`, which is exactly the continued-fraction expansion of `r₀/r₁`.
The parent file's open question OQ-05 (Knuth–Yao–Dixon analysis) asks:

> The Knuth–Yao–Dixon analysis gives the distribution of quotients
> `qᵢ = ⌊r_{i-1}/rᵢ⌋` — are these Gauss–Kuzmin distributed? What does a formal proof
> require?

The **Gauss–Kuzmin distribution** is the limiting law of continued-fraction digits: for
a "random" real number the probability that a given partial quotient equals `k ≥ 1` is

      P(k) = log₂(1 + 1 / (k·(k+2))).

The full statement that the Euclidean quotients *are* asymptotically Gauss–Kuzmin
distributed (the Gauss–Kuzmin–Lévy theorem) rests on the ergodicity of the Gauss map
`x ↦ {1/x}` and the invariance of the Gauss measure `dμ = 1/(ln 2)·dx/(1+x)` — ergodic
machinery not yet available in Mathlib.  This file formalizes the **foundational
prerequisite** that the question's premise rests on, and gives a concrete first answer to
"what does a formal proof require":

> **The Gauss–Kuzmin weights P(k) form a genuine probability distribution:**
> every `P(k) > 0`, and `∑_{k≥1} P(k) = 1`.

## What is proved

* `gaussKuzmin_pos` — every weight is strictly positive.
* `gaussKuzmin_eq_sub` — the key telescoping identity `P(k) = G(k) − G(k+1)`, where
  `G(k) = log₂((k+2)/(k+1))`, obtained from `1 + 1/((k+1)(k+3)) = (k+2)²/((k+1)(k+3))`.
* `gaussKuzmin_partial` — the closed form of the partial sums:
  `∑_{n<N} P(n) = 1 − log₂((N+2)/(N+1))`.
* `gaussKuzmin_partial_tendsto_one` / `gaussKuzmin_tsum` — the partial sums converge to
  `1`, and `∑' k, P(k) = 1`: the weights are normalized.
* `gaussKuzmin_summable` — the family is summable.

(The terms are indexed by `n : ℕ` with the quotient value `k = n+1 ≥ 1`, so
`gaussKuzmin n = P(n+1) = log₂(1 + 1/((n+1)(n+3)))`.)

Tags: number-theory, continued-fractions, gauss-kuzmin, euclidean-algorithm, probability,
telescoping
-/

namespace GCDAlgorithmOQ05

open Real Filter Topology Finset

/-- The Gauss–Kuzmin weight for quotient value `k = n + 1 ≥ 1`:
    `P(k) = log₂(1 + 1/(k(k+2)))`, here with `k = n+1` so the denominator is
    `(n+1)(n+3)`. -/
noncomputable def gaussKuzmin (n : ℕ) : ℝ :=
  logb 2 (1 + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 3)))

/-- The telescoping antiderivative `G(n) = log₂((n+2)/(n+1))`. -/
noncomputable def G (n : ℕ) : ℝ := logb 2 (((n : ℝ) + 2) / ((n : ℝ) + 1))

/-- **Each Gauss–Kuzmin weight is strictly positive.**  The argument
    `1 + 1/((n+1)(n+3)) > 1` and the base `2 > 1`, so the logarithm is positive. -/
theorem gaussKuzmin_pos (n : ℕ) : 0 < gaussKuzmin n := by
  unfold gaussKuzmin
  apply Real.logb_pos (by norm_num)
  have h : 0 < 1 / (((n : ℝ) + 1) * ((n : ℝ) + 3)) := by positivity
  linarith

/-- **The telescoping identity.**  `P(n) = G(n) − G(n+1)`, since
    `1 + 1/((n+1)(n+3)) = (n+2)²/((n+1)(n+3)) = ((n+2)/(n+1)) / ((n+3)/(n+2))`. -/
theorem gaussKuzmin_eq_sub (n : ℕ) : gaussKuzmin n = G n - G (n + 1) := by
  unfold gaussKuzmin G
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  push_cast
  rw [← Real.logb_div (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- **Closed form of the partial sums.**  `∑_{n<N} P(n) = G(0) − G(N) = 1 − log₂((N+2)/(N+1))`. -/
theorem gaussKuzmin_partial (N : ℕ) :
    ∑ n ∈ Finset.range N, gaussKuzmin n = G 0 - G N := by
  simp_rw [gaussKuzmin_eq_sub]
  exact Finset.sum_range_sub' G N

/-- `G(0) = log₂(2/1) = 1`. -/
theorem G_zero : G 0 = 1 := by
  unfold G
  norm_num

/-- `G(n) ≥ 0`, since `(n+2)/(n+1) ≥ 1` and the base exceeds `1`. -/
theorem G_nonneg (n : ℕ) : 0 ≤ G n := by
  unfold G
  apply Real.logb_nonneg (by norm_num)
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- `G(n) → 0` as `n → ∞`, because `(n+2)/(n+1) → 1` and `log₂` is continuous at `1`. -/
theorem G_tendsto_zero : Tendsto (fun n : ℕ => G n) atTop (𝓝 0) := by
  unfold G
  -- (n+2)/(n+1) = 1 + 1/(n+1) → 1
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have hre : (fun n : ℕ => ((n : ℝ) + 2) / ((n : ℝ) + 1))
        = (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) := by
      funext n
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hre]
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds.add h0)
  -- log₂ is continuous at 1
  have hlog : ContinuousAt (fun x : ℝ => Real.logb 2 x) 1 := by
    unfold Real.logb
    exact (Real.continuousAt_log (by norm_num)).div_const _
  have := hlog.tendsto.comp hratio
  rwa [Real.logb_one] at this

/-- **The partial sums converge to `1`.** -/
theorem gaussKuzmin_partial_tendsto_one :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, gaussKuzmin n) atTop (𝓝 1) := by
  have heq : (fun N : ℕ => ∑ n ∈ Finset.range N, gaussKuzmin n) = fun N : ℕ => G 0 - G N :=
    funext gaussKuzmin_partial
  rw [heq, G_zero]
  simpa using tendsto_const_nhds.sub G_tendsto_zero

/-- **The Gauss–Kuzmin weights are summable.**  Each partial sum `1 − G(N) ≤ 1`. -/
theorem gaussKuzmin_summable : Summable gaussKuzmin :=
  summable_of_sum_range_le (c := 1) (fun n => (gaussKuzmin_pos n).le) (fun N => by
    rw [gaussKuzmin_partial, G_zero]
    linarith [G_nonneg N])

/-- **Normalization: `∑_{k≥1} P(k) = 1`.**  Together with `gaussKuzmin_pos`, this is the
    statement that the Gauss–Kuzmin weights form a genuine probability distribution — the
    foundational prerequisite the OQ-05 question rests on. -/
theorem gaussKuzmin_tsum : ∑' n, gaussKuzmin n = 1 :=
  tendsto_nhds_unique gaussKuzmin_summable.hasSum.tendsto_sum_nat
    gaussKuzmin_partial_tendsto_one

#check @gaussKuzmin_pos
#check @gaussKuzmin_partial
#check @gaussKuzmin_tsum
#check @gaussKuzmin_summable

/-
## Summary

Proved (0 sorries, 0 axioms — self-contained, imports only Mathlib):

* `gaussKuzmin_pos` — every weight `P(k) > 0`.
* `gaussKuzmin_eq_sub` — telescoping identity `P(n) = G(n) − G(n+1)`.
* `gaussKuzmin_partial` — `∑_{n<N} P(n) = 1 − log₂((N+2)/(N+1))`.
* `gaussKuzmin_partial_tendsto_one` / `gaussKuzmin_summable` / `gaussKuzmin_tsum` — the
  weights are summable and sum to `1`.

Hence the Gauss–Kuzmin weights form a genuine probability distribution.  This is the
normalization prerequisite behind OQ-05's question "are the Euclidean quotients Gauss–Kuzmin
distributed?"; the asymptotic-distribution statement itself (Gauss–Kuzmin–Lévy) further
requires the ergodicity of the Gauss map and the invariance of the Gauss measure, which are
not yet in Mathlib.
-/

end GCDAlgorithmOQ05
