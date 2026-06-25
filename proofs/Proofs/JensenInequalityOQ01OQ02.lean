/-
# Weighted Power-Mean Monotonicity in the Exponent

For nonnegative data `z : ι → ℝ` with nonnegative weights `w` summing to `1`, the
**weighted power mean**

    M_r(z; w) = (∑ᵢ wᵢ · zᵢ^r) ^ (1/r)

is monotone *nondecreasing in the exponent* `r`: if `0 < p ≤ q` then `M_p ≤ M_q`.

This is the classical generalized-mean (Hölder/power-mean) inequality. Mathlib provides the
convexity engine for power maps — `Real.rpow_arith_mean_le_arith_mean_rpow`, the finite weighted
Jensen inequality `(∑ wᵢ zᵢ)^t ≤ ∑ wᵢ zᵢ^t` for `t ≥ 1` — but it does **not** package the
monotonicity of `M_r` in `r`. That derivation is the content of this file.

## The argument

Write `A = ∑ wᵢ zᵢ^p` and `B = ∑ wᵢ zᵢ^q`. Put `t = q/p ≥ 1`. Applying Jensen with exponent `t`
to the data `yᵢ = zᵢ^p`:

    A^t = (∑ wᵢ zᵢ^p)^t ≤ ∑ wᵢ (zᵢ^p)^t = ∑ wᵢ zᵢ^{p·t} = ∑ wᵢ zᵢ^q = B,

using `(zᵢ^p)^t = zᵢ^{p·t}` and `p·t = q`. Raising the monotone inequality `A^t ≤ B` to the power
`1/q ≥ 0` and simplifying `(A^t)^{1/q} = A^{t/q} = A^{1/p}` gives `M_p = A^{1/p} ≤ B^{1/q} = M_q`.

## Main results

* `powerMean_le_powerMean` — weighted power-mean monotonicity for `0 < p ≤ q`.
* `weighted_am_le_qm` — the arithmetic mean ≤ quadratic mean specialization (`p = 1`, `q = 2`).

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib

open Finset Real

variable {ι : Type*} {s : Finset ι} {w z : ι → ℝ}

/-- **Weighted power-mean monotonicity** (positive exponents).
For nonnegative data `z` with nonnegative weights `w` summing to `1`, and `0 < p ≤ q`, the
weighted power mean is monotone nondecreasing in the exponent:
`(∑ᵢ wᵢ · zᵢ^p)^(1/p) ≤ (∑ᵢ wᵢ · zᵢ^q)^(1/q)`. -/
theorem powerMean_le_powerMean
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) ≤ (∑ i ∈ s, w i * z i ^ q) ^ (1 / q) := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hp' : p ≠ 0 := hp.ne'
  have hq' : q ≠ 0 := hq.ne'
  -- the exponent ratio `t = q / p ≥ 1`
  set t : ℝ := q / p with ht
  have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hp]; linarith
  -- nonnegativity facts
  have hzp : ∀ i ∈ s, 0 ≤ z i ^ p := fun i hi => rpow_nonneg (hz i hi) p
  have hA : 0 ≤ ∑ i ∈ s, w i * z i ^ p :=
    sum_nonneg fun i hi => mul_nonneg (hw i hi) (hzp i hi)
  -- `p · t = q`, so `(zᵢ^p)^t = zᵢ^q`
  have hpt : p * t = q := by
    rw [ht]; field_simp
  have hrw : ∀ i ∈ s, w i * (z i ^ p) ^ t = w i * z i ^ q := by
    intro i hi
    rw [← Real.rpow_mul (hz i hi) p t, hpt]
  -- Jensen with exponent `t` applied to `yᵢ = zᵢ^p`
  have key : (∑ i ∈ s, w i * z i ^ p) ^ t ≤ ∑ i ∈ s, w i * z i ^ q := by
    calc (∑ i ∈ s, w i * z i ^ p) ^ t
        ≤ ∑ i ∈ s, w i * (z i ^ p) ^ t :=
          Real.rpow_arith_mean_le_arith_mean_rpow s w (fun i => z i ^ p) hw hw' hzp ht1
      _ = ∑ i ∈ s, w i * z i ^ q := sum_congr rfl hrw
  -- raise `A^t ≤ B` to the power `1/q`, then rewrite `(A^t)^{1/q} = A^{1/p}`
  have hexp : t * (1 / q) = 1 / p := by
    rw [ht]; field_simp
  calc (∑ i ∈ s, w i * z i ^ p) ^ (1 / p)
      = ((∑ i ∈ s, w i * z i ^ p) ^ t) ^ (1 / q) := by
        rw [← Real.rpow_mul hA, hexp]
    _ ≤ (∑ i ∈ s, w i * z i ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (by positivity) key (by positivity)

/-- **Arithmetic mean ≤ quadratic mean** (weighted), the `p = 1, q = 2` specialization of
power-mean monotonicity:
`∑ᵢ wᵢ zᵢ ≤ (∑ᵢ wᵢ zᵢ²)^(1/2)`. -/
theorem weighted_am_le_qm
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∑ i ∈ s, w i * z i ≤ (∑ i ∈ s, w i * z i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h := powerMean_le_powerMean hw hw' hz (p := 1) (q := 2) one_pos (by norm_num)
  -- normalize the `M_1` side: `(∑ wᵢ zᵢ^(1:ℝ))^(1/1) = ∑ wᵢ zᵢ`
  simpa using h
