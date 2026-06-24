import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
# Divergence of the Reciprocals of the Odd Numbers

## What This Proves

The classical harmonic-series entries (`HarmonicDivergence`, `…OQ01–OQ05`) study
`∑ 1/n`.  This entry isolates the **odd-indexed subseries**

  `∑_{k≥0} 1/(2k+1) = 1 + 1/3 + 1/5 + 1/7 + …`

and proves it diverges.  The point is that throwing away *half* the harmonic
terms — every even denominator — does not restore summability: the surviving
"thinner" series is still divergent.

## The argument

The proof is a clean comparison with the harmonic series itself.  For every `k`,

  `1/(2k+1) ≥ 1/(2k+2) = (1/2)·1/(k+1)`,

because `2k+1 ≤ 2k+2`.  Two consequences:

* **Quantitative** (`oddPartial_ge_half_harmonic`): the `N`-term partial sum of
  the odd reciprocals dominates *half* the corresponding harmonic partial sum,
  `∑_{k<N} 1/(2k+1) ≥ (1/2)·∑_{k<N} 1/(k+1)`.  Since the harmonic partial sums
  are unbounded, so are these.

* **Qualitative** (`not_summable_one_div_odd`): if `∑ 1/(2k+1)` converged, the
  termwise-smaller nonnegative series `∑ 1/(2k+2) = (1/2)∑ 1/(k+1)` would
  converge too, contradicting `Real.not_summable_one_div_natCast`.

From non-summability and nonnegativity we read off divergence to `+∞`
(`tendsto_oddPartial_atTop`).

## Relation to Mathlib

Mathlib proves `¬ Summable (fun n => 1/n)` (`Real.not_summable_one_div_natCast`)
and the divergence of the *full* harmonic partial sums, but it does not record
the divergence of the odd-reciprocal subseries.  We obtain it here by an
elementary comparison, with an explicit partial-sum lower bound as a bonus.

## Status
- [x] Complete proof (0 sorries, 0 axioms)
- [x] Headline `not_summable_one_div_odd` plus quantitative partial-sum bound
-/

namespace HarmonicDivergenceOQ06

open Finset Filter Topology

/-- **Termwise comparison.** Each odd reciprocal dominates half the corresponding
harmonic term: `(1/2)·1/(k+1) ≤ 1/(2k+1)`, because `2k+1 ≤ 2(k+1)`. -/
theorem half_harmonic_le_odd (k : ℕ) :
    (1 : ℝ) / 2 * (1 / ((k : ℝ) + 1)) ≤ 1 / (2 * (k : ℝ) + 1) := by
  have hk1 : (0 : ℝ) < 2 * k + 1 := by positivity
  have hle : (2 : ℝ) * k + 1 ≤ 2 * (k + 1) := by linarith
  have e : (1 : ℝ) / 2 * (1 / ((k : ℝ) + 1)) = 1 / (2 * ((k : ℝ) + 1)) := by
    rw [div_mul_div_comm, one_mul]
  rw [e]
  exact one_div_le_one_div_of_le hk1 hle

/-- **Quantitative partial-sum bound.** The `N`-term partial sum of the odd
reciprocals is at least half the `N`-term harmonic partial sum:

  `(1/2)·∑_{k<N} 1/(k+1) ≤ ∑_{k<N} 1/(2k+1)`. -/
theorem oddPartial_ge_half_harmonic (N : ℕ) :
    (1 : ℝ) / 2 * ∑ k ∈ range N, (1 / ((k : ℝ) + 1)) ≤
      ∑ k ∈ range N, (1 / (2 * (k : ℝ) + 1)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => half_harmonic_le_odd k)

/-- **Headline: the reciprocals of the odd numbers are not summable.**

`∑_{k≥0} 1/(2k+1) = 1 + 1/3 + 1/5 + …` diverges. -/
theorem not_summable_one_div_odd :
    ¬ Summable (fun n : ℕ => (1 : ℝ) / (2 * n + 1)) := by
  intro h
  -- Compare against the termwise-smaller even reciprocals `1/(2n+2)`.
  have hcmp : Summable (fun n : ℕ => (1 : ℝ) / (2 * n + 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
    have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
    have hle : (2 : ℝ) * n + 1 ≤ 2 * n + 2 := by linarith
    exact one_div_le_one_div_of_le hpos hle
  -- `2 · 1/(2n+2) = 1/(n+1)`, so the harmonic series (shifted) would converge.
  have hharm : Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
    have h2 := hcmp.mul_left 2
    refine h2.congr (fun n => ?_)
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  -- Shift back to `1/n` and contradict the harmonic non-summability lemma.
  have hnat : Summable (fun n : ℕ => (1 : ℝ) / n) := by
    rw [← summable_nat_add_iff 1]
    simpa using hharm
  exact Real.not_summable_one_div_natCast hnat

/-- **Divergence to `+∞`.** The partial sums `∑_{k<N} 1/(2k+1)` tend to `+∞`. -/
theorem tendsto_oddPartial_atTop :
    Tendsto (fun N => ∑ k ∈ range N, (1 : ℝ) / (2 * k + 1)) atTop atTop := by
  have hnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / (2 * n + 1) := fun n => by positivity
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp not_summable_one_div_odd

end HarmonicDivergenceOQ06
