/-
# Sharpness of the Generalized Minkowski Inequality: Homogeneity, Definiteness, and Saturation on a Common Ray

The sibling file `JensenInequalityOQ01OQ01OQ01OQ02` proves the finite-family Minkowski inequality
— subadditivity of the discrete `ℓᵖ` norm `‖g‖_p = (∑ᵢ g(i)ᵖ)^{1/p}` over an arbitrary finite
family of nonnegative vectors:

    ‖∑ⱼ Fⱼ‖_p ≤ ∑ⱼ ‖Fⱼ‖_p.

This file records *when that inequality is sharp* and the structural facts that make the discrete
`ℓᵖ` norm a seminorm:

* **Positive homogeneity** `Lpnorm_smul`: `‖c · g‖_p = c · ‖g‖_p` for `c ≥ 0`.
* **Definiteness** `Lpnorm_eq_zero_iff`: `‖g‖_p = 0 ↔ g` vanishes on the coordinate set.
* **Saturation on a common ray** `minkowski_finset_eq_of_common_ray`: if every vector of the family
  is a nonnegative multiple `Fⱼ = cⱼ · h` of a single direction `h`, then Minkowski holds with
  *equality*, `‖∑ⱼ Fⱼ‖_p = ∑ⱼ ‖Fⱼ‖_p`.

The saturation result is the "easy half" of the equality case of Minkowski's inequality: it
exhibits the extremal configurations — collinear (proportional) vectors — on which the triangle
inequality for the `ℓᵖ` norm is tight, for every `p > 0`. (The converse, that equality *forces*
proportionality, requires `p > 1` and the strict convexity of `t ↦ tᵖ`, and is left open.)

Mathlib provides neither the elementary closed-form homogeneity/definiteness of this discrete
`ℓᵖ` norm nor the saturation characterization; this file supplies them, self-contained.

## Main results

* `Lpnorm`                            — the discrete `ℓᵖ` norm `(∑ᵢ g(i)ᵖ)^{1/p}`.
* `Lpnorm_smul`                       — positive homogeneity `‖c · g‖_p = c · ‖g‖_p`.
* `Lpnorm_eq_zero_iff`                — definiteness: the norm vanishes iff the vector does.
* `minkowski_finset_eq_of_common_ray` — **Minkowski saturates on a common ray** `Fⱼ = cⱼ · h`.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib

open Finset

namespace JensenMinkowskiSharp

variable {ι κ : Type*} {s : Finset ι} {p : ℝ}

/-- The unnormalised discrete `ℓᵖ` "norm" of a vector `g : ι → ℝ` over the coordinate set `s`:
`Lpnorm s p g = (∑ i ∈ s, g i ^ p) ^ (1/p)`. -/
noncomputable def Lpnorm (s : Finset ι) (p : ℝ) (g : ι → ℝ) : ℝ :=
  (∑ i ∈ s, g i ^ p) ^ (1 / p)

/-- For `a ≥ 0` and `p ≠ 0`, `(aᵖ)^{1/p} = a`: the reciprocal power inverts the `p`-th power. -/
private theorem rpow_pow_inv {a : ℝ} (ha : 0 ≤ a) (hp : p ≠ 0) : (a ^ p) ^ (1 / p) = a := by
  rw [← Real.rpow_mul ha, mul_one_div, div_self hp, Real.rpow_one]

/-- **Positive homogeneity of the discrete `ℓᵖ` norm.** For `p > 0`, a scalar `c ≥ 0`, and a
vector `g` nonnegative on `s`, scaling the vector scales its norm: `‖c · g‖_p = c · ‖g‖_p`. -/
theorem Lpnorm_smul (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) {g : ι → ℝ} (hg : ∀ i ∈ s, 0 ≤ g i) :
    Lpnorm s p (fun i => c * g i) = c * Lpnorm s p g := by
  unfold Lpnorm
  have hpow : ∀ i ∈ s, (c * g i) ^ p = c ^ p * g i ^ p :=
    fun i hi => Real.mul_rpow hc (hg i hi)
  rw [Finset.sum_congr rfl hpow, ← Finset.mul_sum,
    Real.mul_rpow (Real.rpow_nonneg hc p) (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hg i hi) p),
    rpow_pow_inv hc hp.ne']

/-- **Definiteness of the discrete `ℓᵖ` norm.** For `p > 0` and a vector `g` nonnegative on `s`,
the norm `‖g‖_p` is zero exactly when `g` vanishes everywhere on `s`. -/
theorem Lpnorm_eq_zero_iff (hp : 0 < p) {g : ι → ℝ} (hg : ∀ i ∈ s, 0 ≤ g i) :
    Lpnorm s p g = 0 ↔ ∀ i ∈ s, g i = 0 := by
  unfold Lpnorm
  rw [Real.rpow_eq_zero_iff_of_nonneg
        (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hg i hi) p),
    and_iff_left (one_div_ne_zero hp.ne'),
    Finset.sum_eq_zero_iff_of_nonneg fun i hi => Real.rpow_nonneg (hg i hi) p]
  exact forall₂_congr fun i hi =>
    by rw [Real.rpow_eq_zero_iff_of_nonneg (hg i hi), and_iff_left hp.ne']

/-- **Saturation of the finite-family Minkowski inequality on a common ray.** If every vector of a
finite family is a nonnegative multiple `F j = c j · h` of a single direction `h` (with `c j ≥ 0`
and `h` nonnegative on `s`), then the Minkowski inequality holds with *equality*:

    Lpnorm s p (fun i => ∑ j ∈ t, c j * h i) = ∑ j ∈ t, Lpnorm s p (fun i => c j * h i).

This identifies the extremal configurations — collinear vectors — on which the `ℓᵖ` triangle
inequality is tight, for every `p > 0`. Both sides equal `(∑ j ∈ t, c j) · ‖h‖_p`. -/
theorem minkowski_finset_eq_of_common_ray (hp : 0 < p) (t : Finset κ) (c : κ → ℝ) (h : ι → ℝ)
    (hc : ∀ j ∈ t, 0 ≤ c j) (hh : ∀ i ∈ s, 0 ≤ h i) :
    Lpnorm s p (fun i => ∑ j ∈ t, c j * h i)
      = ∑ j ∈ t, Lpnorm s p (fun i => c j * h i) := by
  have hsum : 0 ≤ ∑ j ∈ t, c j := Finset.sum_nonneg hc
  have hL : (fun i => ∑ j ∈ t, c j * h i) = (fun i => (∑ j ∈ t, c j) * h i) := by
    funext i; rw [← Finset.sum_mul]
  rw [hL, Lpnorm_smul hp hsum hh,
    Finset.sum_congr rfl fun j hj => Lpnorm_smul hp (hc j hj) hh, ← Finset.sum_mul]

end JensenMinkowskiSharp
