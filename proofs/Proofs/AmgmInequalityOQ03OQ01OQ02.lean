/-
# Generalized Mean Inequality for Arbitrary Real Exponents

## Open Question: amgm-inequality-oq-03-oq-01-oq-02

This file fills the explicit `TODO` in `Mathlib.Analysis.MeanInequalitiesPow`:

> generalized mean inequality with any `p ≤ q`, including negative numbers;

Mathlib currently proves the generalized mean inequality only for the special
case `p = 1` (`Real.arith_mean_le_rpow_mean`). The full monotonicity of the
weighted power mean in its exponent — for **all** real `p ≤ q` with
`p, q ≠ 0`, including negative exponents and the sign-crossing case — is the
content of this file.

## Main result

For non-negative weights `w` summing to `1` and strictly positive values `z`,
the weighted power mean

  M_p(z, w) = (∑ᵢ wᵢ zᵢ^p)^(1/p)

is monotone in `p`:  for `p ≤ q` (both nonzero),  M_p ≤ M_q.

The headline theorem `Real.rpow_mean_le_rpow_mean` is stated directly on the
raw expressions `(∑ i ∈ s, w i * z i ^ p) ^ (1 / p)`, matching the idiom of the
existing `Real.arith_mean_le_rpow_mean`, so it is ready to be contributed
upstream.

## Proof structure

The argument dispatches on the signs of `p` and `q`, using the weighted
geometric mean `G(z, w) = ∏ᵢ zᵢ^{wᵢ}` (the `p → 0` limit) as the bridge:

1. `0 < p ≤ q`  — Jensen's inequality for the convex map `t ↦ t^{q/p}`
   (`Real.rpow_arith_mean_le_arith_mean_rpow`).
2. `p ≤ q < 0`  — duality `M_p(z) = M_{-p}(z⁻¹)⁻¹` reduces to case 1 on `z⁻¹`.
3. `p < 0 < q`  — sandwich `M_p ≤ G ≤ M_q`, where `G ≤ M_q` is weighted AM–GM
   applied to `zᵢ^q`, and `M_p ≤ G` is its dual on `z⁻¹`.

All three cases are then combined by trichotomy.

## References

- Hardy, G.H., Littlewood, J.E., Pólya, G. (1934). *Inequalities*. Cambridge.
- Mathlib: `Mathlib.Analysis.MeanInequalitiesPow` (the `TODO` this addresses)
- Mathlib: `Real.geom_mean_le_arith_mean_weighted`, `Real.arith_mean_le_rpow_mean`
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Finset

namespace Real

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-- The weighted power mean of order `p`, as the raw expression
`(∑ i ∈ s, w i * z i ^ p) ^ (1 / p)`.  Kept `private` and definitionally
transparent so the public theorems can be stated on the bare expression. -/
private noncomputable def pmean (p : ℝ) : ℝ := (∑ i ∈ s, w i * z i ^ p) ^ (1 / p)

/-- Antitonicity of inversion on the positive reals: `a ≤ b ⟹ b⁻¹ ≤ a⁻¹`. -/
private lemma inv_anti_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le ha hab

/-- The weighted sum `∑ wᵢ zᵢ^p` is nonnegative. -/
private lemma weighted_sum_nonneg
    (hw : ∀ i ∈ s, 0 ≤ w i) (hz : ∀ i ∈ s, 0 < z i) (p : ℝ) :
    0 ≤ ∑ i ∈ s, w i * z i ^ p :=
  Finset.sum_nonneg fun i hi =>
    mul_nonneg (hw i hi) (Real.rpow_nonneg (le_of_lt (hz i hi)) p)

/-- The weighted sum `∑ wᵢ zᵢ^p` is strictly positive when the weights sum to
`1` and all values are positive. -/
private lemma weighted_sum_pos
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) (p : ℝ) :
    0 < ∑ i ∈ s, w i * z i ^ p := by
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push_neg at h
    have hw_zero : ∀ i ∈ s, w i = 0 := fun i hi => le_antisymm (h i hi) (hw i hi)
    have hsum : ∑ i ∈ s, w i = 0 := Finset.sum_eq_zero hw_zero
    rw [hsum] at hw'
    exact one_ne_zero hw'.symm
  exact lt_of_lt_of_le
    (mul_pos hwi₀ (Real.rpow_pos_of_pos (hz i₀ hi₀) p))
    (Finset.single_le_sum
      (fun i hi => mul_nonneg (hw i hi) (Real.rpow_nonneg (le_of_lt (hz i hi)) p)) hi₀)

/-- The weighted power mean is strictly positive. -/
private lemma pmean_pos
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) (p : ℝ) :
    0 < pmean s w z p :=
  Real.rpow_pos_of_pos (weighted_sum_pos s w z hw hw' hz p) (1 / p)

/-- **Duality identity**: `M_p(z) = M_{-p}(z⁻¹)⁻¹`.

The power mean of order `p` equals the reciprocal of the power mean of order
`-p` applied to the reciprocal values. -/
private lemma pmean_neg_inv
    (hw : ∀ i ∈ s, 0 ≤ w i) (hz : ∀ i ∈ s, 0 < z i) (p : ℝ) :
    pmean s w z p = (pmean s w (fun i => (z i)⁻¹) (-p))⁻¹ := by
  simp only [pmean]
  have sum_eq : ∑ i ∈ s, w i * (z i)⁻¹ ^ (-p) = ∑ i ∈ s, w i * z i ^ p := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [Real.inv_rpow (le_of_lt (hz i hi)) (-p),
        Real.rpow_neg (le_of_lt (hz i hi)) p, inv_inv]
  have hA_nn : 0 ≤ ∑ i ∈ s, w i * z i ^ p := weighted_sum_nonneg s w z hw hz p
  rw [sum_eq, show (1 : ℝ) / (-p) = -(1 / p) from by ring,
      Real.rpow_neg hA_nn, inv_inv]

/-- **Case 1 (both positive exponents): `0 < p ≤ q ⟹ M_p ≤ M_q`.**

Proved via Jensen's inequality for the convex power map `t ↦ t^{q/p}`. -/
private lemma pmean_mono_pos
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    pmean s w z p ≤ pmean s w z q := by
  simp only [pmean]
  have hq_pos : 0 < q := lt_of_lt_of_le hp hpq
  have hquot : 1 ≤ q / p := by
    rw [le_div_iff₀ hp, one_mul]; exact hpq
  have hzr_nn : ∀ i ∈ s, 0 ≤ (fun i => z i ^ p) i :=
    fun i hi => Real.rpow_nonneg (le_of_lt (hz i hi)) p
  -- Jensen: (∑ wᵢ (zᵢ^p))^(q/p) ≤ ∑ wᵢ (zᵢ^p)^(q/p)
  have jensen : (∑ i ∈ s, w i * z i ^ p) ^ (q / p) ≤ ∑ i ∈ s, w i * (z i ^ p) ^ (q / p) :=
    Real.rpow_arith_mean_le_arith_mean_rpow s w (fun i => z i ^ p) hw hw' hzr_nn hquot
  -- (zᵢ^p)^(q/p) = zᵢ^q
  have simp_sum : ∑ i ∈ s, w i * (z i ^ p) ^ (q / p) = ∑ i ∈ s, w i * z i ^ q :=
    Finset.sum_congr rfl fun i hi => by
      congr 1
      rw [← Real.rpow_mul (le_of_lt (hz i hi))]
      congr 1
      field_simp
  rw [simp_sum] at jensen
  have hsum_p : 0 ≤ ∑ i ∈ s, w i * z i ^ p := weighted_sum_nonneg s w z hw hz p
  -- raise both sides to 1/q
  have hmono : ((∑ i ∈ s, w i * z i ^ p) ^ (q / p)) ^ (1 / q) ≤
               (∑ i ∈ s, w i * z i ^ q) ^ (1 / q) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hsum_p _) jensen (by positivity)
  have lhs_simp : ((∑ i ∈ s, w i * z i ^ p) ^ (q / p)) ^ (1 / q) =
                  (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) := by
    rw [← Real.rpow_mul hsum_p]
    congr 1
    field_simp
  rw [lhs_simp] at hmono
  exact hmono

/-- **Case 2 (both negative exponents): `p ≤ q < 0 ⟹ M_p ≤ M_q`.**

Reduces to Case 1 on the reciprocal values via the duality identity. -/
private lemma pmean_mono_neg
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {p q : ℝ} (hpq : p ≤ q) (hq : q < 0) :
    pmean s w z p ≤ pmean s w z q := by
  have hp : p < 0 := lt_of_le_of_lt hpq hq
  have hzinv : ∀ i ∈ s, 0 < (fun i => (z i)⁻¹) i := fun i hi => inv_pos.mpr (hz i hi)
  -- M_{-q}(z⁻¹) ≤ M_{-p}(z⁻¹) by Case 1 (since 0 < -q ≤ -p)
  have h_mono : pmean s w (fun i => (z i)⁻¹) (-q) ≤ pmean s w (fun i => (z i)⁻¹) (-p) :=
    pmean_mono_pos s w (fun i => (z i)⁻¹) hw hw' hzinv (neg_pos.mpr hq) (neg_le_neg hpq)
  have h_neg_q_pos : 0 < pmean s w (fun i => (z i)⁻¹) (-q) :=
    pmean_pos s w (fun i => (z i)⁻¹) hw hw' hzinv (-q)
  rw [pmean_neg_inv s w z hw hz p, pmean_neg_inv s w z hw hz q]
  exact inv_anti_of_le h_neg_q_pos h_mono

/-- The weighted geometric mean is strictly positive. -/
private lemma geom_mean_pos (hz : ∀ i ∈ s, 0 < z i) :
    0 < ∏ i ∈ s, z i ^ w i :=
  Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hz i hi) (w i)

/-- **Geometric mean ≤ power mean for positive exponent: `0 < q ⟹ G ≤ M_q`.**

Weighted AM–GM applied to the values `zᵢ^q`. -/
private lemma geom_mean_le_pmean_of_pos
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {q : ℝ} (hq : 0 < q) :
    (∏ i ∈ s, z i ^ w i) ≤ pmean s w z q := by
  simp only [pmean]
  have hzq : ∀ i ∈ s, 0 ≤ (fun i => z i ^ q) i :=
    fun i hi => Real.rpow_nonneg (le_of_lt (hz i hi)) q
  -- AM–GM on zᵢ^q: ∏ (zᵢ^q)^wᵢ ≤ ∑ wᵢ (zᵢ^q)
  have amgm := Real.geom_mean_le_arith_mean_weighted s w (fun i => z i ^ q) hw hw' hzq
  -- ∏ (zᵢ^q)^wᵢ = (∏ zᵢ^wᵢ)^q
  have hLHS : ∏ i ∈ s, (z i ^ q) ^ w i = (∏ i ∈ s, z i ^ w i) ^ q := by
    rw [← Real.finset_prod_rpow s (fun i => z i ^ w i)
          (fun i hi => Real.rpow_nonneg (le_of_lt (hz i hi)) (w i)) q]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Real.rpow_mul (le_of_lt (hz i hi)), ← Real.rpow_mul (le_of_lt (hz i hi)), mul_comm]
  rw [hLHS] at amgm
  have hGM : 0 ≤ ∏ i ∈ s, z i ^ w i :=
    Finset.prod_nonneg fun i hi => Real.rpow_nonneg (le_of_lt (hz i hi)) (w i)
  -- raise to 1/q > 0
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hGM q) amgm (le_of_lt (by positivity : (0:ℝ) < 1 / q))
  rwa [← Real.rpow_mul hGM, mul_one_div_cancel (ne_of_gt hq), Real.rpow_one] at h

/-- **Power mean ≤ geometric mean for negative exponent: `p < 0 ⟹ M_p ≤ G`.**

The dual of `geom_mean_le_pmean_of_pos` on the reciprocal values. -/
private lemma pmean_le_geom_mean_of_neg
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {p : ℝ} (hp : p < 0) :
    pmean s w z p ≤ ∏ i ∈ s, z i ^ w i := by
  have hzinv : ∀ i ∈ s, 0 < (fun i => (z i)⁻¹) i := fun i hi => inv_pos.mpr (hz i hi)
  -- G(z⁻¹) ≤ M_{-p}(z⁻¹) since -p > 0
  have hgm := geom_mean_le_pmean_of_pos s w (fun i => (z i)⁻¹) hw hw' hzinv (neg_pos.mpr hp)
  -- G(z⁻¹) = G(z)⁻¹
  have geom_inv : (∏ i ∈ s, (z i)⁻¹ ^ w i) = (∏ i ∈ s, z i ^ w i)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.inv_rpow (le_of_lt (hz i hi)) (w i)
  rw [geom_inv] at hgm
  rw [pmean_neg_inv s w z hw hz p]
  -- goal: (M_{-p}(z⁻¹))⁻¹ ≤ G(z),  from  G(z)⁻¹ ≤ M_{-p}(z⁻¹)
  have hGM_pos : 0 < ∏ i ∈ s, z i ^ w i := geom_mean_pos s w z hz
  have key := inv_anti_of_le (inv_pos.mpr hGM_pos) hgm
  rwa [inv_inv] at key

/-- **Generalized mean inequality for arbitrary real exponents.**

For non-negative weights `w` with `∑ i ∈ s, w i = 1`, strictly positive values
`z`, and nonzero exponents `p ≤ q`, the weighted power means satisfy

  `(∑ i ∈ s, w i * z i ^ p) ^ (1 / p) ≤ (∑ i ∈ s, w i * z i ^ q) ^ (1 / q)`.

This is the generalization of `Real.arith_mean_le_rpow_mean` (the `p = 1` case)
to all real `p ≤ q`, including negative exponents — the content of the `TODO`
in `Mathlib.Analysis.MeanInequalitiesPow`. -/
theorem rpow_mean_le_rpow_mean
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≤ q) :
    (∑ i ∈ s, w i * z i ^ p) ^ (1 / p) ≤ (∑ i ∈ s, w i * z i ^ q) ^ (1 / q) := by
  -- the goal is `pmean s w z p ≤ pmean s w z q` by definitional unfolding
  show pmean s w z p ≤ pmean s w z q
  rcases lt_trichotomy p 0 with hpneg | hp0 | hppos
  · rcases lt_trichotomy q 0 with hqneg | hq0 | hqpos
    · exact pmean_mono_neg s w z hw hw' hz hpq hqneg
    · exact absurd hq0 hq
    · exact (pmean_le_geom_mean_of_neg s w z hw hw' hz hpneg).trans
        (geom_mean_le_pmean_of_pos s w z hw hw' hz hqpos)
  · exact absurd hp0 hp
  · exact pmean_mono_pos s w z hw hw' hz hppos hpq

end Real
