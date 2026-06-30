import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Proofs.CauchySchwarzOQ02OQ04OQ01

/-
# Cauchy-Schwarz OQ-02 → OQ-04 → OQ-01 → OQ-01: Kittaneh's numerical-radius inequality

## Overview

The *numerical radius* of a bounded operator `T` on a Hilbert space is
`w(T) = sup_{‖x‖=1} ‖⟪T x, x⟫‖`.  The elementary bound `w(T) ≤ ‖T‖` is immediate
from Cauchy-Schwarz.  Kittaneh (F. Kittaneh, *Studia Math.* **158** (2003), 11-17)
proved the genuine *strengthening*

      w(T)² ≤ ½ (‖T‖² + ‖T²‖).

Because `‖T²‖ ≤ ‖T‖²` always (submultiplicativity), Kittaneh's bound never exceeds
`‖T‖²`, so it refines `w(T) ≤ ‖T‖`, and the refinement is strict whenever
`‖T²‖ < ‖T‖²` (e.g. for a nilpotent `T`).

This file derives the *pointwise* form of Kittaneh's inequality

      ‖⟪T x, x⟫‖² ≤ ½ (‖T‖² + ‖T²‖)          (‖x‖ = 1),

directly from **Buzano's inequality** (`CauchySchwarzOQ02OQ04OQ01`), which is the
parent problem.  The key move is the *adjoint trick*: apply Buzano with unit vector
`e = x` and the two vectors `T x` and `T† x`.  The two adjoint identities

  * `⟪x, T† x⟫ = ⟪T x, x⟫`     (so the Buzano left side is `2 ‖⟪T x, x⟫‖²`),
  * `⟪T x, T† x⟫ = ⟪T² x, x⟫`  (so the Buzano cross term is controlled by `‖T²‖`),

turn the geometric two-vector Buzano bound into the operator inequality.  The
remaining factor `‖T x‖ · ‖T† x‖` is bounded by `‖T‖²` using `‖T†‖ = ‖T‖`.

Kittaneh's numerical-radius inequality is not in Mathlib.

## Main Results (6 theorems, 0 definitions, 0 sorries)

1. `opNorm_sq_le`          — ‖T²‖ ≤ ‖T‖² (submultiplicativity, used for the refinement)
2. `kittaneh_inner_sq`     — ‖⟪T x, x⟫‖² ≤ ½(‖T‖² + ‖T²‖) for unit `x`   [HEADLINE]
3. `kittaneh_inner_le`     — ‖⟪T x, x⟫‖ ≤ √(½(‖T‖² + ‖T²‖))             (root form)
4. `inner_diag_le_opNorm`  — ‖⟪T x, x⟫‖ ≤ ‖T‖ (recovers `w(T) ≤ ‖T‖` from Kittaneh)
5. `inner_diag_nilpotent`  — `T² = 0` ⟹ ‖⟪T x, x⟫‖ ≤ ‖T‖/√2 (strict refinement)
6. `kittaneh_inner_sq_le_opNorm_sq` — ½(‖T‖² + ‖T²‖) ≤ ‖T‖² (Kittaneh ≤ trivial bound)
-/

noncomputable section

open RCLike ComplexConjugate ContinuousLinearMap

namespace CauchySchwarzKittaneh

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

omit [CompleteSpace E] in
/-- **Submultiplicativity.**  `‖T²‖ ≤ ‖T‖²`.  This is what makes Kittaneh's bound a
genuine refinement of `w(T) ≤ ‖T‖`: the right-hand side `½(‖T‖² + ‖T²‖)` is always
sandwiched between `‖T²‖` and `‖T‖²`. -/
theorem opNorm_sq_le (T : E →L[𝕜] E) : ‖T ^ 2‖ ≤ ‖T‖ ^ 2 := by
  rw [pow_two, pow_two]
  exact norm_mul_le T T

/-- The adjoint preserves the operator norm: `‖T†‖ = ‖T‖`. -/
private theorem norm_adjoint (T : E →L[𝕜] E) : ‖adjoint T‖ = ‖T‖ :=
  LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint T

/-- **Kittaneh's inequality (pointwise form).**  For a unit vector `x` and a bounded
operator `T` on a Hilbert space,

      ‖⟪T x, x⟫‖² ≤ ½ (‖T‖² + ‖T²‖).

Taking the supremum over unit `x` gives Kittaneh's numerical-radius bound
`w(T)² ≤ ½(‖T‖² + ‖T²‖)`.

*Proof.*  Apply Buzano's inequality (`buzano_inequality`) with the unit vector `x`
and the two vectors `T x`, `T† x`:

      2 ‖⟪T x, x⟫‖ ‖⟪x, T† x⟫‖ ≤ ‖T x‖ ‖T† x‖ + ‖⟪T x, T† x⟫‖.

The adjoint identity `⟪x, T† x⟫ = ⟪T x, x⟫` makes the left side `2 ‖⟪T x, x⟫‖²`.  On
the right, `‖T x‖ ‖T† x‖ ≤ ‖T‖²` (unit `x`, `‖T†‖ = ‖T‖`), while `⟪T x, T† x⟫ = ⟪T² x, x⟫`
gives `‖⟪T x, T† x⟫‖ ≤ ‖T²‖`.  Hence `2 ‖⟪T x, x⟫‖² ≤ ‖T‖² + ‖T²‖`. -/
theorem kittaneh_inner_sq {x : E} (hx : ‖x‖ = 1) (T : E →L[𝕜] E) :
    ‖⟪T x, x⟫‖ ^ 2 ≤ (‖T‖ ^ 2 + ‖T ^ 2‖) / 2 := by
  -- Buzano with e = x, first vector `T x`, second vector `T† x`.
  have hb := CauchySchwarzBuzano.buzano_inequality (𝕜 := 𝕜) hx (T x) (adjoint T x)
  -- Left-side identity: ⟪x, T† x⟫ = ⟪T x, x⟫.
  have e1 : ‖⟪x, adjoint T x⟫‖ = ‖⟪T x, x⟫‖ := by rw [adjoint_inner_right]
  rw [e1] at hb
  -- Norm of the adjoint.
  have hadjnorm : ‖adjoint T‖ = ‖T‖ := norm_adjoint T
  -- ‖T x‖ ≤ ‖T‖ and ‖T† x‖ ≤ ‖T‖ (unit x).
  have hTx : ‖T x‖ ≤ ‖T‖ := by have := T.le_opNorm x; rwa [hx, mul_one] at this
  have hadj : ‖adjoint T x‖ ≤ ‖T‖ := by
    rw [← hadjnorm]; have := (adjoint T).le_opNorm x; rwa [hx, mul_one] at this
  -- First right-hand term: ‖T x‖ ‖T† x‖ ≤ ‖T‖².
  have e2 : ‖T x‖ * ‖adjoint T x‖ ≤ ‖T‖ ^ 2 := by
    have h := mul_le_mul hTx hadj (norm_nonneg _) (norm_nonneg T)
    rwa [← pow_two] at h
  -- Cross term: ⟪T x, T† x⟫ = ⟪T² x, x⟫, controlled by ‖T²‖.
  have e3 : ‖⟪T x, adjoint T x⟫‖ ≤ ‖T ^ 2‖ := by
    rw [adjoint_inner_right]
    calc ‖⟪T (T x), x⟫‖
        ≤ ‖T (T x)‖ * ‖x‖ := norm_inner_le_norm _ _
      _ = ‖T (T x)‖ := by rw [hx, mul_one]
      _ = ‖(T ^ 2) x‖ := by rw [pow_two, ContinuousLinearMap.mul_apply]
      _ ≤ ‖T ^ 2‖ := by have := (T ^ 2).le_opNorm x; rwa [hx, mul_one] at this
  -- Combine and clear the factor of two.
  have hcomb : 2 * ‖⟪T x, x⟫‖ * ‖⟪T x, x⟫‖ ≤ ‖T‖ ^ 2 + ‖T ^ 2‖ :=
    le_trans hb (add_le_add e2 e3)
  nlinarith [hcomb]

/-- **Kittaneh's inequality (root form).**  `‖⟪T x, x⟫‖ ≤ √(½(‖T‖² + ‖T²‖))`. -/
theorem kittaneh_inner_le {x : E} (hx : ‖x‖ = 1) (T : E →L[𝕜] E) :
    ‖⟪T x, x⟫‖ ≤ Real.sqrt ((‖T‖ ^ 2 + ‖T ^ 2‖) / 2) := by
  rw [show ‖⟪T x, x⟫‖ = Real.sqrt (‖⟪T x, x⟫‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  exact Real.sqrt_le_sqrt (kittaneh_inner_sq hx T)

omit [CompleteSpace E] in
/-- The Kittaneh bound never exceeds the trivial bound: `½(‖T‖² + ‖T²‖) ≤ ‖T‖²`. -/
theorem kittaneh_inner_sq_le_opNorm_sq (T : E →L[𝕜] E) :
    (‖T‖ ^ 2 + ‖T ^ 2‖) / 2 ≤ ‖T‖ ^ 2 := by
  have h := opNorm_sq_le T
  linarith

/-- **Recovery of `w(T) ≤ ‖T‖`.**  Kittaneh's inequality implies the elementary
numerical-radius bound `‖⟪T x, x⟫‖ ≤ ‖T‖` for every unit vector `x`. -/
theorem inner_diag_le_opNorm {x : E} (hx : ‖x‖ = 1) (T : E →L[𝕜] E) :
    ‖⟪T x, x⟫‖ ≤ ‖T‖ := by
  have hN : ‖⟪T x, x⟫‖ ^ 2 ≤ ‖T‖ ^ 2 :=
    le_trans (kittaneh_inner_sq hx T) (kittaneh_inner_sq_le_opNorm_sq T)
  calc ‖⟪T x, x⟫‖ = Real.sqrt (‖⟪T x, x⟫‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖T‖ ^ 2) := Real.sqrt_le_sqrt hN
    _ = ‖T‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Strict refinement for nilpotent operators.**  If `T² = 0` then Kittaneh's
inequality collapses to `‖⟪T x, x⟫‖ ≤ ‖T‖/√2`, strictly better than `‖T‖` whenever
`T ≠ 0`.  (For the `2×2` Jordan nilpotent this gives `w(T) ≤ 1/√2`, improving the
trivial `w(T) ≤ ‖T‖ = 1`.) -/
theorem inner_diag_nilpotent {x : E} (hx : ‖x‖ = 1) (T : E →L[𝕜] E) (hT2 : T ^ 2 = 0) :
    ‖⟪T x, x⟫‖ ≤ ‖T‖ / Real.sqrt 2 := by
  have h := kittaneh_inner_sq hx T
  rw [hT2, norm_zero, add_zero] at h
  calc ‖⟪T x, x⟫‖ = Real.sqrt (‖⟪T x, x⟫‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖T‖ ^ 2 / 2) := Real.sqrt_le_sqrt h
    _ = ‖T‖ / Real.sqrt 2 := by
        rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end CauchySchwarzKittaneh
