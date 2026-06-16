import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Menelaus's Theorem (collinearity via signed side ratios)

## What This Proves
For a triangle `A B C` and points
* `X` on line `BC` with `X = (1-t)·B + t·C`,
* `Y` on line `CA` with `Y = (1-u)·C + u·A`,
* `Z` on line `AB` with `Z = (1-v)·A + v·B`,

the three points `X, Y, Z` are collinear **iff** the product of signed side ratios

  (BX/XC) · (CY/YA) · (AZ/ZB) = (t/(1-t)) · (u/(1-u)) · (v/(1-v)) = -1.

This is the transversal companion of Ceva's theorem (`CevasTheorem.lean`), which
characterises *concurrency* of cevians by the same product equalling `+1`.

## Approach
Work in the affine plane `ℝ × ℝ`. Collinearity of three points is encoded by the
vanishing of the signed-area determinant `collinearDet`. The mathematical heart is the
factorisation

  collinearDet X Y Z = (t·u·v + (1-t)·(1-u)·(1-v)) · collinearDet A B C,

a pure polynomial identity discharged by `ring`. For a non-degenerate triangle the base
determinant is non-zero, so collinearity is equivalent to the scalar factor vanishing,
i.e. `t·u·v = -(1-t)(1-u)(1-v)`, which `field_simp` shows is exactly the signed-ratio
product being `-1`.

## Status
- [x] Signed-area determinant and collinearity predicate
- [x] Determinant factorisation (the geometric content)
- [x] Main equivalence: collinearity ↔ product = -1
- [x] Directional corollaries and a concrete numerical instance
- [x] 0 sorries, 0 axioms

## Mathlib Dependencies
Real arithmetic, `field_simp`, `ring`, `linear_combination`, `mul_eq_zero`.

Note: Menelaus's theorem is **not** a named Mathlib result.
-/

namespace MenelausTheorem

set_option linter.unusedVariables false

/-- A point in the affine plane. -/
abbrev Pt := ℝ × ℝ

/-- Twice the signed area of triangle `P Q R`: the `2×2` determinant of the edge
    vectors `Q - P` and `R - P`. It vanishes exactly when the points are collinear. -/
def collinearDet (P Q R : Pt) : ℝ :=
  (Q.1 - P.1) * (R.2 - P.2) - (Q.2 - P.2) * (R.1 - P.1)

/-- Three points are collinear when their signed-area determinant vanishes. -/
def Collinear3 (P Q R : Pt) : Prop := collinearDet P Q R = 0

/-- Configuration for Menelaus: a triangle `A B C` with transversal division
    parameters `t, u, v`. Each parameter must avoid `1` so the corresponding signed
    ratio `t/(1-t)` is defined, and the triangle must be non-degenerate. -/
structure MenelausConfig where
  A : Pt
  B : Pt
  C : Pt
  t : ℝ
  u : ℝ
  v : ℝ
  t_ne_1 : t ≠ 1
  u_ne_1 : u ≠ 1
  v_ne_1 : v ≠ 1
  nondegen : collinearDet A B C ≠ 0

/-- `X = (1-t)·B + t·C` divides line `BC`. -/
def ptX (cfg : MenelausConfig) : Pt :=
  ((1 - cfg.t) * cfg.B.1 + cfg.t * cfg.C.1, (1 - cfg.t) * cfg.B.2 + cfg.t * cfg.C.2)

/-- `Y = (1-u)·C + u·A` divides line `CA`. -/
def ptY (cfg : MenelausConfig) : Pt :=
  ((1 - cfg.u) * cfg.C.1 + cfg.u * cfg.A.1, (1 - cfg.u) * cfg.C.2 + cfg.u * cfg.A.2)

/-- `Z = (1-v)·A + v·B` divides line `AB`. -/
def ptZ (cfg : MenelausConfig) : Pt :=
  ((1 - cfg.v) * cfg.A.1 + cfg.v * cfg.B.1, (1 - cfg.v) * cfg.A.2 + cfg.v * cfg.B.2)

/-- The product of the three signed side ratios
    `(BX/XC) · (CY/YA) · (AZ/ZB) = (t/(1-t)) · (u/(1-u)) · (v/(1-v))`. -/
noncomputable def menelausProduct (cfg : MenelausConfig) : ℝ :=
  (cfg.t / (1 - cfg.t)) * (cfg.u / (1 - cfg.u)) * (cfg.v / (1 - cfg.v))

/-- **Geometric content of Menelaus.** The collinearity determinant of the three
    division points factors as the Menelaus scalar `t·u·v + (1-t)(1-u)(1-v)` times the
    signed area of the underlying triangle. Pure polynomial identity. -/
theorem collinearDet_factor (cfg : MenelausConfig) :
    collinearDet (ptX cfg) (ptY cfg) (ptZ cfg)
      = (cfg.t * cfg.u * cfg.v + (1 - cfg.t) * (1 - cfg.u) * (1 - cfg.v))
        * collinearDet cfg.A cfg.B cfg.C := by
  simp only [collinearDet, ptX, ptY, ptZ]
  ring

/-- **Menelaus's Theorem.** For a non-degenerate triangle, the transversal points
    `X, Y, Z` are collinear iff the product of signed side ratios equals `-1`. -/
theorem menelaus (cfg : MenelausConfig) :
    Collinear3 (ptX cfg) (ptY cfg) (ptZ cfg) ↔ menelausProduct cfg = -1 := by
  have ht : (1 : ℝ) - cfg.t ≠ 0 := sub_ne_zero.mpr (Ne.symm cfg.t_ne_1)
  have hu : (1 : ℝ) - cfg.u ≠ 0 := sub_ne_zero.mpr (Ne.symm cfg.u_ne_1)
  have hv : (1 : ℝ) - cfg.v ≠ 0 := sub_ne_zero.mpr (Ne.symm cfg.v_ne_1)
  unfold Collinear3
  rw [collinearDet_factor, mul_eq_zero, or_iff_left cfg.nondegen]
  unfold menelausProduct
  rw [div_mul_div_comm, div_mul_div_comm,
    div_eq_iff (mul_ne_zero (mul_ne_zero ht hu) hv)]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Collinearity of the transversal points implies the signed-ratio product is `-1`. -/
theorem product_of_collinear (cfg : MenelausConfig)
    (h : Collinear3 (ptX cfg) (ptY cfg) (ptZ cfg)) : menelausProduct cfg = -1 :=
  (menelaus cfg).mp h

/-- If the signed-ratio product is `-1`, the transversal points are collinear. -/
theorem collinear_of_product (cfg : MenelausConfig)
    (h : menelausProduct cfg = -1) : Collinear3 (ptX cfg) (ptY cfg) (ptZ cfg) :=
  (menelaus cfg).mpr h

/-- A concrete instance: triangle `(0,0),(1,0),(0,1)` with `t = u = 2`, `v = -1/3`
    gives product `-1`, hence the three division points are collinear. -/
theorem menelaus_example :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = -1 ∧ Collinear3 (ptX cfg) (ptY cfg) (ptZ cfg) := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 2, u := 2, v := -1/3,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ?_⟩
  · unfold menelausProduct; norm_num
  · apply collinear_of_product; unfold menelausProduct; norm_num

end MenelausTheorem
