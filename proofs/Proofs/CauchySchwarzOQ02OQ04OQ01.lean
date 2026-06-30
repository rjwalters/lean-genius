import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Cauchy-Schwarz OQ-02 → OQ-04 → OQ-01: Buzano's Inequality

## Overview

The Cauchy-Schwarz inequality `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` bounds a single inner product.
Buzano's inequality (M. L. Buzano, 1974) is a genuine *strengthening* that bounds the
product of two inner products against a fixed unit vector `e`:

      ‖⟪x, e⟫‖ * ‖⟪e, y⟫‖ ≤ (‖x‖ * ‖y‖ + ‖⟪x, y⟫‖) / 2          (‖e‖ = 1).

Cauchy-Schwarz is the special case `e = x / ‖x‖` (proved here as
`buzano_recovers_cauchy_schwarz`), so Buzano is strictly more general.

This file develops Buzano's inequality on an inner product space over `𝕜 = ℝ` or `ℂ`
(`RCLike`), as a follow-up to the operator-norm / Kadison–Schwarz material in
`CauchySchwarzOQ02OQ04`.  The proof is elementary and self-contained, resting on a
single geometric idea:

  * **Reflection.**  For a unit vector `e`, the map `y ↦ 2⟪e, y⟫ • e - y` is the
    reflection of `y` through the line `span e`.  It is an *isometry*
    (`reflection_isometry`), so applying Cauchy-Schwarz to `⟪x, 2⟪e, y⟫ • e - y⟫`
    bounds `‖2⟪x, e⟫⟪e, y⟫ - ⟪x, y⟫‖` by `‖x‖ * ‖y‖`.  The triangle inequality then
    isolates `2‖⟪x, e⟫‖ * ‖⟪e, y⟫‖`.

Buzano's inequality is not in Mathlib.

## Main Results (7 theorems, 0 definitions, 0 sorries)

1. `inner_reflection_eq`   — ⟪x, 2⟪e,y⟫•e - y⟫ = 2⟪x,e⟫⟪e,y⟫ - ⟪x,y⟫ (algebraic)
2. `reflection_isometry`   — ‖2⟪e,y⟫•e - y‖ = ‖y‖ for a unit vector `e`
3. `buzano_inner_bound`    — ‖2⟪x,e⟫⟪e,y⟫ - ⟪x,y⟫‖ ≤ ‖x‖‖y‖
4. `buzano_inequality`     — 2‖⟪x,e⟫‖‖⟪e,y⟫‖ ≤ ‖x‖‖y‖ + ‖⟪x,y⟫‖
5. `buzano_inequality_div` — ‖⟪x,e⟫‖‖⟪e,y⟫‖ ≤ (‖x‖‖y‖ + ‖⟪x,y⟫‖)/2
6. `buzano_self`           — ‖⟪x,e⟫‖ ≤ ‖x‖ (Cauchy-Schwarz against a unit `e`)
7. `buzano_recovers_cauchy_schwarz` — Buzano ⟹ ‖⟪x,y⟫‖ ≤ ‖x‖‖y‖ (general CS)
-/

noncomputable section

open RCLike ComplexConjugate

namespace CauchySchwarzBuzano

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **Reflection identity.**  Expanding the inner product against the reflected
vector `2⟪e, y⟫ • e - y` produces the combination that drives Buzano's inequality.
This step is purely algebraic (sesquilinearity); no unit-vector hypothesis is needed. -/
theorem inner_reflection_eq (x e y : E) :
    ⟪x, (2 * ⟪e, y⟫) • e - y⟫ = 2 * ⟪x, e⟫ * ⟪e, y⟫ - ⟪x, y⟫ := by
  rw [inner_sub_right, inner_smul_right]
  ring

/-- **Reflection is an isometry.**  For a unit vector `e`, the reflection of `y`
through the line `span e`, namely `2⟪e, y⟫ • e - y`, has the same norm as `y`.

The proof computes `‖2⟪e, y⟫ • e - y‖²` via the polarization formula `norm_sub_sq`;
the cross term `2 · re⟪2⟪e, y⟫ • e, y⟫` cancels exactly with `‖2⟪e, y⟫ • e‖²`. -/
theorem reflection_isometry {e : E} (he : ‖e‖ = 1) (y : E) :
    ‖(2 * ⟪e, y⟫) • e - y‖ = ‖y‖ := by
  -- The cross term `re ⟪2⟪e,y⟫ • e, y⟫` equals `2‖⟪e,y⟫‖²`.
  have hcross : re ⟪(2 * ⟪e, y⟫) • e, y⟫ = 2 * ‖⟪e, y⟫‖ ^ 2 := by
    rw [inner_smul_left, map_mul (starRingEnd 𝕜), mul_assoc, RCLike.conj_mul]
    simp only [RCLike.conj_ofNat, pow_two, RCLike.mul_re, RCLike.ofReal_re,
      RCLike.ofReal_im, RCLike.ofNat_re, RCLike.ofNat_im, mul_zero, zero_mul, sub_zero]
  -- Reduce the norm equality to the equality of squares.
  rw [← Real.sqrt_sq (norm_nonneg ((2 * ⟪e, y⟫) • e - y)), ← Real.sqrt_sq (norm_nonneg y)]
  congr 1
  rw [norm_sub_sq (𝕜 := 𝕜), norm_smul, he, hcross, norm_mul, RCLike.norm_ofNat]
  ring

/-- **Reflected Cauchy-Schwarz bound.**  Applying Cauchy-Schwarz to `x` and the
reflection of `y`, then using that the reflection preserves norm, bounds the
key combination by `‖x‖ * ‖y‖`. -/
theorem buzano_inner_bound {e : E} (he : ‖e‖ = 1) (x y : E) :
    ‖2 * ⟪x, e⟫ * ⟪e, y⟫ - ⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  rw [← inner_reflection_eq]
  calc ‖⟪x, (2 * ⟪e, y⟫) • e - y⟫‖
      ≤ ‖x‖ * ‖(2 * ⟪e, y⟫) • e - y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [reflection_isometry he]

/-- **Buzano's inequality.**  For a unit vector `e`,

      2 ‖⟪x, e⟫‖ ‖⟪e, y⟫‖ ≤ ‖x‖ ‖y‖ + ‖⟪x, y⟫‖.

The triangle inequality splits `2⟪x, e⟫⟪e, y⟫` off the bounded combination
`2⟪x, e⟫⟪e, y⟫ - ⟪x, y⟫` from `buzano_inner_bound`. -/
theorem buzano_inequality {e : E} (he : ‖e‖ = 1) (x y : E) :
    2 * ‖⟪x, e⟫‖ * ‖⟪e, y⟫‖ ≤ ‖x‖ * ‖y‖ + ‖⟪x, y⟫‖ := by
  have hb := buzano_inner_bound (𝕜 := 𝕜) he x y
  have htri := norm_sub_norm_le (2 * ⟪x, e⟫ * ⟪e, y⟫) (⟪x, y⟫ : 𝕜)
  have hnorm : ‖2 * ⟪x, e⟫ * ⟪e, y⟫‖ = 2 * ‖⟪x, e⟫‖ * ‖⟪e, y⟫‖ := by
    rw [norm_mul, norm_mul, RCLike.norm_ofNat]
  rw [hnorm] at htri
  linarith

/-- **Buzano's inequality, halved form.**  The product of the two inner products is
bounded by the average of `‖x‖ ‖y‖` and `‖⟪x, y⟫‖`. -/
theorem buzano_inequality_div {e : E} (he : ‖e‖ = 1) (x y : E) :
    ‖⟪x, e⟫‖ * ‖⟪e, y⟫‖ ≤ (‖x‖ * ‖y‖ + ‖⟪x, y⟫‖) / 2 := by
  have h := buzano_inequality (𝕜 := 𝕜) he x y
  linarith

/-- **Self / consistency form.**  Taking `y = x` in Buzano recovers Cauchy-Schwarz
against the unit vector `e`: `‖⟪x, e⟫‖ ≤ ‖x‖`. -/
theorem buzano_self {e : E} (he : ‖e‖ = 1) (x : E) :
    ‖⟪x, e⟫‖ ≤ ‖x‖ := by
  have h := buzano_inequality (𝕜 := 𝕜) he x x
  have hsymm : ‖⟪e, x⟫‖ = ‖⟪x, e⟫‖ := by
    rw [← RCLike.norm_conj, inner_conj_symm]
  have hxx : ‖⟪x, x⟫‖ = ‖x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x)]
  rw [hsymm, hxx] at h
  nlinarith [h, norm_nonneg (⟪x, e⟫ : 𝕜), norm_nonneg x]

/-- **Buzano recovers Cauchy-Schwarz.**  Choosing the unit vector `e = ‖x‖⁻¹ • x`
collapses Buzano's inequality to the classical Cauchy-Schwarz inequality
`‖⟪x, y⟫‖ ≤ ‖x‖ ‖y‖`, witnessing that Buzano is a strict generalization. -/
theorem buzano_recovers_cauchy_schwarz (x y : E) (hx : x ≠ 0) :
    ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hne : ‖x‖ ≠ 0 := hxpos.ne'
  set c : 𝕜 := ((‖x‖⁻¹ : ℝ) : 𝕜) with hc
  set e : E := c • x with he_def
  have hcnorm : ‖c‖ = ‖x‖⁻¹ := by
    rw [hc, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, hcnorm]
    exact inv_mul_cancel₀ hne
  -- ⟪x, e⟫ = ‖x‖ (as a real coercion)
  have hxe : ⟪x, e⟫ = ((‖x‖ : ℝ) : 𝕜) := by
    rw [he_def, inner_smul_right, hc, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      ← RCLike.ofReal_mul]
    congr 1
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  -- ⟪e, y⟫ = c * ⟪x, y⟫
  have hey : ⟪e, y⟫ = c * ⟪x, y⟫ := by
    rw [he_def, inner_smul_left, hc, RCLike.conj_ofReal]
  have h := buzano_inequality (𝕜 := 𝕜) he x y
  rw [hxe, hey, RCLike.norm_ofReal, abs_of_nonneg hxpos.le, norm_mul, hcnorm] at h
  have key : 2 * ‖x‖ * (‖x‖⁻¹ * ‖⟪x, y⟫‖) = 2 * ‖⟪x, y⟫‖ := by
    rw [show 2 * ‖x‖ * (‖x‖⁻¹ * ‖⟪x, y⟫‖) = 2 * ‖⟪x, y⟫‖ * (‖x‖ * ‖x‖⁻¹) by ring,
      mul_inv_cancel₀ hne, mul_one]
  rw [key] at h
  linarith

end CauchySchwarzBuzano
