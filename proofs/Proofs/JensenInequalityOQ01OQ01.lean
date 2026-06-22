/-
# Young's Inequality and its Equality Case, from Weighted AM–GM

Young's inequality states that for Hölder-conjugate exponents `p, q` (so `1/p + 1/q = 1`,
`p, q > 1`) and nonnegative reals `a, b`,

    a * b ≤ aᵖ / p + bᵍ / q,

with **equality exactly when `aᵖ = bᵍ`**. Mathlib provides the inequality
(`Real.young_inequality_of_nonneg`) but not its equality case; this file supplies it.

The whole statement is the two-term weighted arithmetic–geometric mean inequality in disguise:
taking weights `wₓ = 1/p`, `w_y = 1/q` (which sum to `1`) and data `x = aᵖ`, `y = bᵍ`, the weighted
geometric mean `x^{wₓ} · y^{w_y} = (aᵖ)^{1/p} · (bᵍ)^{1/q} = a · b` and the weighted arithmetic
mean `wₓ x + w_y y = aᵖ/p + bᵍ/q`. So Young's inequality, and its equality case, are exactly the
two-variable weighted AM–GM and *its* equality case — which we obtain from the parent file's
`weighted_amgm_eq_iff`.

## Main results

* `amgm_two_weighted_eq_iff` — the two-variable weighted AM–GM equality case
  `x^{wₓ} y^{w_y} = wₓ x + w_y y ↔ x = y`, specialized from `weighted_amgm_eq_iff`.
* `young_le` — Young's inequality `a b ≤ aᵖ/p + bᵍ/q` (re-export).
* `young_eq_iff` — **Young's equality case**: `a b = aᵖ/p + bᵍ/q ↔ aᵖ = bᵍ`.
* `young_lt_of_ne` — the strict form when `aᵖ ≠ bᵍ`.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.JensenInequalityOQ01

open Finset Real

/-- The **two-variable weighted AM–GM equality case**: for strictly positive weights `wₓ, w_y`
summing to `1` and nonnegative data `x, y`, the weighted geometric mean equals the weighted
arithmetic mean exactly when `x = y`. This is `weighted_amgm_eq_iff` (parent file) on a two-element
index set. -/
theorem amgm_two_weighted_eq_iff {wx wy x y : ℝ} (hwx : 0 < wx) (hwy : 0 < wy)
    (hw : wx + wy = 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ wx * y ^ wy = wx * x + wy * y ↔ x = y := by
  have hwsum : ∑ i ∈ (Finset.univ : Finset (Fin 2)), ![wx, wy] i = 1 := by
    rw [Fin.sum_univ_two]; exact hw
  have hwpos : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < ![wx, wy] i := by
    intro i _; fin_cases i
    · simpa using hwx
    · simpa using hwy
  have hznn : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ ![x, y] i := by
    intro i _; fin_cases i
    · simpa using hx
    · simpa using hy
  have key := weighted_amgm_eq_iff hwpos hwsum hznn
  rw [Fin.prod_univ_two, Fin.sum_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at key
  rw [key]
  constructor
  · intro h; simpa using h 0 (Finset.mem_univ _) 1 (Finset.mem_univ _)
  · intro h j _ k _; fin_cases j <;> fin_cases k <;> simp [h]

/-- **Young's inequality** for nonnegative reals (re-export of `Real.young_inequality_of_nonneg`). -/
theorem young_le {a b p q : ℝ} (hpq : p.HolderConjugate q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb hpq

/-- **Equality case of Young's inequality.** For Hölder-conjugate exponents `p, q` and nonnegative
`a, b`, Young's inequality `a b ≤ aᵖ/p + bᵍ/q` is an equality if and only if `aᵖ = bᵍ`.

The proof applies the two-variable weighted AM–GM equality case with weights `1/p, 1/q` and data
`aᵖ, bᵍ`, using `(aᵖ)^{1/p} = a` (and likewise for `b`). -/
theorem young_eq_iff {a b p q : ℝ} (hpq : p.HolderConjugate q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b = a ^ p / p + b ^ q / q ↔ a ^ p = b ^ q := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hinv : p⁻¹ + q⁻¹ = 1 := (Real.holderConjugate_iff.mp hpq).2
  have hxa : (a ^ p) ^ p⁻¹ = a := by
    rw [← Real.rpow_mul ha, mul_inv_cancel₀ hp.ne', Real.rpow_one]
  have hxb : (b ^ q) ^ q⁻¹ = b := by
    rw [← Real.rpow_mul hb, mul_inv_cancel₀ hq.ne', Real.rpow_one]
  have key := amgm_two_weighted_eq_iff (inv_pos.mpr hp) (inv_pos.mpr hq) hinv
    (Real.rpow_nonneg ha p) (Real.rpow_nonneg hb q)
  rw [hxa, hxb] at key
  rw [show a ^ p / p + b ^ q / q = p⁻¹ * a ^ p + q⁻¹ * b ^ q from by ring]
  exact key

/-- **Strict Young's inequality.** When `aᵖ ≠ bᵍ`, Young's inequality is strict. -/
theorem young_lt_of_ne {a b p q : ℝ} (hpq : p.HolderConjugate q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hne : a ^ p ≠ b ^ q) :
    a * b < a ^ p / p + b ^ q / q :=
  lt_of_le_of_ne (young_le hpq ha hb) fun h => hne ((young_eq_iff hpq ha hb).mp h)
