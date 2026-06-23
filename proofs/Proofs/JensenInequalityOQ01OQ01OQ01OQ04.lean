import Mathlib

/-
# Monotonicity of the Weighted Power Mean in its Exponent

For a finite family of nonnegative reals `x i` (`i ∈ s`) with nonnegative weights `w i`
summing to `1`, the **weighted power mean of exponent `p`** is

    M_p(x) = (∑ i, w i * x i ^ p) ^ (1 / p).

This file proves the classical **power-mean inequality**: the map `p ↦ M_p(x)` is monotone
non-decreasing on `p > 0`,

    0 < p ≤ q  ⟹  M_p(x) ≤ M_q(x).

This single statement contains the comparison of the weighted arithmetic mean `M_1` with every
higher power mean, and in particular the quadratic-mean / arithmetic-mean (QM–AM, or
root-mean-square) inequality. It is the canonical consequence of Jensen's inequality applied to
the convex map `t ↦ tʳ` (`r ≥ 1`), and sits at the head of the AM–GM / Young / Hölder / Minkowski
family developed in the sibling files of this lineage.

Mathlib provides the *single-exponent* Jensen building block
`Real.rpow_arith_mean_le_arith_mean_rpow` — `(∑ w i z i) ^ r ≤ ∑ w i * z i ^ r` for `r ≥ 1` —
but **no closed-form power mean nor its monotonicity in the exponent**; this file supplies them,
self-contained.

## Main results

* `powerMean`               — the weighted power mean `(∑ i, w i * x i ^ p) ^ (1 / p)`.
* `powerMean_nonneg`        — power means of nonnegative data are nonnegative.
* `powerMean_one`           — `M_1` is the weighted arithmetic mean `∑ i, w i * x i`.
* `powerMean_le_powerMean`  — **monotonicity in the exponent**: `0 < p ≤ q ⟹ M_p ≤ M_q`.
* `arith_mean_le_powerMean` — `M_1 ≤ M_p` for `p ≥ 1`: the weighted arithmetic mean is the
  smallest power mean of exponent `≥ 1`.
* `qm_am_inequality`        — the weighted QM–AM inequality `∑ w i x i ≤ (∑ w i x i²)^{1/2}`.

## Strategy

To compare `M_p` and `M_q` for `0 < p ≤ q`, set `r = q / p ≥ 1` and apply
`Real.rpow_arith_mean_le_arith_mean_rpow` to the data `z i = x i ^ p` with exponent `r`:

    (∑ i, w i * x i ^ p) ^ r ≤ ∑ i, w i * (x i ^ p) ^ r = ∑ i, w i * x i ^ q,

using `(x i ^ p) ^ r = x i ^ (p * r) = x i ^ q`.  The left side is `M_p ^ q` and the right side
is `M_q ^ q`; since `q > 0` and both means are nonnegative, `rpow`-monotonicity
(`Real.rpow_le_rpow_iff`) yields `M_p ≤ M_q`.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

open Finset

namespace JensenPowerMean

variable {ι : Type*} {s : Finset ι} {w x : ι → ℝ} {p q : ℝ}

/-- The **weighted power mean of exponent `p`** of a family `x : ι → ℝ` over the finite set `s`
with weights `w`: `powerMean s w x p = (∑ i ∈ s, w i * x i ^ p) ^ (1 / p)`. -/
noncomputable def powerMean (s : Finset ι) (w x : ι → ℝ) (p : ℝ) : ℝ :=
  (∑ i ∈ s, w i * x i ^ p) ^ (1 / p)

/-- The inner sum `∑ i, w i * x i ^ p` of a power mean is nonnegative when the weights and data
are nonnegative. -/
theorem sum_term_nonneg (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ ∑ i ∈ s, w i * x i ^ p :=
  sum_nonneg fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (hx i hi) _)

/-- **Power means of nonnegative data are nonnegative.** -/
theorem powerMean_nonneg (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ powerMean s w x p :=
  Real.rpow_nonneg (sum_term_nonneg hw hx) _

/-- **The power mean of exponent `1` is the weighted arithmetic mean.** -/
theorem powerMean_one : powerMean s w x 1 = ∑ i ∈ s, w i * x i := by
  unfold powerMean
  simp only [Real.rpow_one, div_one]

/-- **Monotonicity of the weighted power mean in the exponent.** For nonnegative weights `w`
summing to `1`, nonnegative data `x`, and exponents `0 < p ≤ q`, the power means satisfy
`M_p ≤ M_q`.

This is the power-mean inequality: among positive exponents, a larger exponent yields a larger
mean. It is proved by applying Jensen's inequality for `t ↦ tʳ` with `r = q / p ≥ 1` to the
powered data `x i ^ p`. -/
theorem powerMean_le_powerMean (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hp : 0 < p) (hpq : p ≤ q) :
    powerMean s w x p ≤ powerMean s w x q := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hpne : p ≠ 0 := hp.ne'
  have hr1 : 1 ≤ q / p := (one_le_div hp).2 hpq
  have hSp_nonneg : 0 ≤ ∑ i ∈ s, w i * x i ^ p := sum_term_nonneg hw hx
  have hSq_nonneg : 0 ≤ ∑ i ∈ s, w i * x i ^ q := sum_term_nonneg hw hx
  -- Jensen for `t ↦ t^(q/p)` (exponent `≥ 1`) applied to the powered data `z i = x i ^ p`.
  have hjensen : (∑ i ∈ s, w i * x i ^ p) ^ (q / p) ≤ ∑ i ∈ s, w i * x i ^ q := by
    have h := Real.rpow_arith_mean_le_arith_mean_rpow s w (fun i => x i ^ p) hw hw'
      (fun i hi => Real.rpow_nonneg (hx i hi) _) hr1
    refine h.trans_eq (sum_congr rfl fun i hi => ?_)
    have hexp : p * (q / p) = q := by field_simp
    rw [← Real.rpow_mul (hx i hi), hexp]
  -- It suffices to compare the `q`-th powers of the two means.
  rw [← Real.rpow_le_rpow_iff (powerMean_nonneg (p := p) hw hx)
        (powerMean_nonneg (p := q) hw hx) hq]
  -- `M_p ^ q = (∑ w x^p)^(q/p)` and `M_q ^ q = ∑ w x^q`, reducing the goal to `hjensen`.
  have hMp : powerMean s w x p ^ q = (∑ i ∈ s, w i * x i ^ p) ^ (q / p) := by
    unfold powerMean
    rw [← Real.rpow_mul hSp_nonneg]
    congr 1
    field_simp
  have hMq : powerMean s w x q ^ q = ∑ i ∈ s, w i * x i ^ q := by
    unfold powerMean
    rw [← Real.rpow_mul hSq_nonneg, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one]
  rw [hMp, hMq]
  exact hjensen

/-- **The weighted arithmetic mean is the smallest power mean of exponent `≥ 1`.** For `p ≥ 1`,
`∑ i, w i * x i ≤ M_p`. This is the `p = 1` slice of `powerMean_le_powerMean`. -/
theorem arith_mean_le_powerMean (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hp : 1 ≤ p) :
    ∑ i ∈ s, w i * x i ≤ powerMean s w x p := by
  rw [← powerMean_one]
  exact powerMean_le_powerMean hw hw' hx one_pos hp

/-- **Weighted QM–AM (root-mean-square) inequality.** The weighted arithmetic mean is at most the
weighted quadratic mean: `∑ i, w i * x i ≤ (∑ i, w i * x i²)^{1/2}`.  This is the `p = 1`, `q = 2`
case of the power-mean inequality. -/
theorem qm_am_inequality (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∑ i ∈ s, w i * x i ≤ (∑ i ∈ s, w i * x i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  arith_mean_le_powerMean (p := 2) hw hw' hx (by norm_num)

end JensenPowerMean
