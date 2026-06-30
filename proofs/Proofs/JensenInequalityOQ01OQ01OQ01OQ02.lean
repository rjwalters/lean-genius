/-
# The Weighted Arithmetic–Harmonic Mean Inequality and its Equality Case
(jensen-inequality-oq-01-oq-01-oq-01-oq-02)

The weighted power-mean `M_r` of strictly positive data `xᵢ` with weights `wᵢ > 0`
summing to `1` is monotone in the exponent `r`. The parent chain established the
weighted AM–GM inequality `weighted_amgm_le` and its equality case
`weighted_amgm_eq_iff` — the `M₀ ≤ M₁` rung (geometric mean ≤ arithmetic mean).

This file proves the rung *below* it, the **arithmetic–harmonic mean inequality**
`M₋₁ ≤ M₁`: the weighted harmonic mean is at most the weighted arithmetic mean,

    (∑ᵢ wᵢ · xᵢ⁻¹)⁻¹  ≤  ∑ᵢ wᵢ · xᵢ ,     with equality iff all the `xᵢ` are equal.

## Proof

Let `G = ∏ᵢ xᵢ^{wᵢ}` be the weighted geometric mean. Two applications of the
parent's weighted AM–GM inequality bracket `G` between the harmonic mean `H` and
the arithmetic mean `A`:

  * to the data `xᵢ`:    `G = ∏ xᵢ^{wᵢ} ≤ ∑ wᵢ xᵢ = A`              (so `G ≤ A`),
  * to the data `xᵢ⁻¹`:  `G⁻¹ = ∏ (xᵢ⁻¹)^{wᵢ} ≤ ∑ wᵢ xᵢ⁻¹ = D`     (so `G⁻¹ ≤ D`),

using `∏ (xᵢ⁻¹)^{wᵢ} = (∏ xᵢ^{wᵢ})⁻¹ = G⁻¹`. Since `G > 0`, the second bound
inverts to the harmonic mean `H = D⁻¹ ≤ G`, and chaining gives `H ≤ G ≤ A`.

The equality case falls out of the same bracketing: `H = A` squeezes `G = A`,
which by `weighted_amgm_eq_iff` forces all `xᵢ` equal; conversely constancy makes
all three means coincide.

This is the `M₋₁ ≤ M₁` power-mean rung, obtained purely from two AM–GM
applications, and is distinct from the Hölder/Minkowski siblings.

## Main results

* `weighted_amhm_le` — the weighted AM–HM inequality `(∑ wᵢ xᵢ⁻¹)⁻¹ ≤ ∑ wᵢ xᵢ`.
* `weighted_amhm_eq_iff` — equality holds **iff all the `xᵢ` are equal**.
* `weighted_amhm_lt_of_ne` — the strict form when two of the `xᵢ` differ.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.JensenInequalityOQ01

open Finset Real

namespace WeightedAMHM

variable {ι : Type*} {s : Finset ι} {w x : ι → ℝ}

/-- The weighted geometric mean of the reciprocals is the reciprocal of the weighted
geometric mean: `∏ (xᵢ⁻¹)^{wᵢ} = (∏ xᵢ^{wᵢ})⁻¹`. -/
private theorem prod_rpow_inv (hx : ∀ i ∈ s, 0 < x i) :
    ∏ i ∈ s, (x i)⁻¹ ^ w i = (∏ i ∈ s, x i ^ w i)⁻¹ := by
  rw [← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i hi => Real.inv_rpow (hx i hi).le _

/-- **Harmonic mean ≤ geometric mean.** Applying the parent's weighted AM–GM
inequality to the reciprocals `xᵢ⁻¹` gives `G⁻¹ ≤ ∑ wᵢ xᵢ⁻¹`, which inverts (using
`G > 0`) to `(∑ wᵢ xᵢ⁻¹)⁻¹ ≤ G`. -/
private theorem harm_le_geom (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * (x i)⁻¹)⁻¹ ≤ ∏ i ∈ s, x i ^ w i := by
  have hGpos : 0 < ∏ i ∈ s, x i ^ w i :=
    Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hx i hi) _
  have hGinvD : (∏ i ∈ s, x i ^ w i)⁻¹ ≤ ∑ i ∈ s, w i * (x i)⁻¹ := by
    have h := weighted_amgm_le (z := fun i => (x i)⁻¹) hw hw'
      (fun i hi => inv_nonneg.mpr (hx i hi).le)
    rwa [prod_rpow_inv hx] at h
  have h2 := inv_anti₀ (inv_pos.mpr hGpos) hGinvD
  rwa [inv_inv] at h2

/-- **The weighted arithmetic–harmonic mean inequality.** For nonnegative weights
summing to `1` and strictly positive data, the weighted harmonic mean is at most the
weighted arithmetic mean. -/
theorem weighted_amhm_le (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * (x i)⁻¹)⁻¹ ≤ ∑ i ∈ s, w i * x i :=
  le_trans (harm_le_geom hw hw' hx)
    (weighted_amgm_le hw hw' (fun i hi => (hx i hi).le))

/-- **Equality case of the weighted AM–HM inequality.** With strictly positive weights
summing to `1` and strictly positive data, the harmonic and arithmetic means coincide
**iff all the data are equal**.

Forward: the bracketing `H ≤ G ≤ A` squeezes `G = A`, and `weighted_amgm_eq_iff`
turns that into constancy. Backward: constancy makes both AM–GM applications
equalities, so `H = G = A`. -/
theorem weighted_amhm_eq_iff (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 < x i) :
    (∑ i ∈ s, w i * (x i)⁻¹)⁻¹ = ∑ i ∈ s, w i * x i ↔ ∀ j ∈ s, ∀ k ∈ s, x j = x k := by
  constructor
  · intro hEq
    -- `G ≤ A` and `H ≤ G` with `H = A` squeeze `G = A`.
    have hGA : ∏ i ∈ s, x i ^ w i ≤ ∑ i ∈ s, w i * x i :=
      weighted_amgm_le (fun i hi => (hw i hi).le) hw' (fun i hi => (hx i hi).le)
    have hHG : (∑ i ∈ s, w i * (x i)⁻¹)⁻¹ ≤ ∏ i ∈ s, x i ^ w i :=
      harm_le_geom (fun i hi => (hw i hi).le) hw' hx
    have hGAeq : ∏ i ∈ s, x i ^ w i = ∑ i ∈ s, w i * x i := by
      refine le_antisymm hGA ?_
      calc ∑ i ∈ s, w i * x i = (∑ i ∈ s, w i * (x i)⁻¹)⁻¹ := hEq.symm
        _ ≤ ∏ i ∈ s, x i ^ w i := hHG
    exact (weighted_amgm_eq_iff hw hw' (fun i hi => (hx i hi).le)).mp hGAeq
  · intro hconst
    -- Both AM–GM applications become equalities, so `H = G⁻¹⁻¹ = A`.
    have hGA : ∏ i ∈ s, x i ^ w i = ∑ i ∈ s, w i * x i :=
      (weighted_amgm_eq_iff hw hw' (fun i hi => (hx i hi).le)).mpr hconst
    have hDeq : ∑ i ∈ s, w i * (x i)⁻¹ = (∏ i ∈ s, x i ^ w i)⁻¹ := by
      rw [← prod_rpow_inv hx]
      exact ((weighted_amgm_eq_iff hw hw' (fun i hi => inv_nonneg.mpr (hx i hi).le)).mpr
        (fun j hj k hk => by rw [hconst j hj k hk])).symm
    rw [hDeq, inv_inv]; exact hGA

/-- **Strict weighted AM–HM inequality.** If two of the data values differ, the
weighted harmonic mean is *strictly* less than the weighted arithmetic mean. -/
theorem weighted_amhm_lt_of_ne (hw : ∀ i ∈ s, 0 < w i) (hw' : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 < x i) (hne : ∃ j ∈ s, ∃ k ∈ s, x j ≠ x k) :
    (∑ i ∈ s, w i * (x i)⁻¹)⁻¹ < ∑ i ∈ s, w i * x i := by
  refine lt_of_le_of_ne (weighted_amhm_le (fun i hi => (hw i hi).le) hw' hx) fun h => ?_
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  exact hjk ((weighted_amhm_eq_iff hw hw' hx).mp h j hj k hk)

end WeightedAMHM
