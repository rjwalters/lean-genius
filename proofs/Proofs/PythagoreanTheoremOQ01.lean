/-
# Pythagorean Theorem OQ-01: The Simplest Proof — Einstein's Similar-Triangles Argument

## The Open Question

> *What's the simplest possible proof of the Pythagorean theorem?*
> (Candidates include Einstein's similar-triangles proof.)

The proof Albert Einstein reportedly discovered as a boy is widely regarded as one of
the most economical. It uses **no auxiliary construction other than a single altitude**,
and a single physical principle:

> **The area of any planar figure is proportional to the square of any one of its
> linear dimensions**, with the *same* proportionality constant for all figures of the
> *same shape* (i.e. similar figures).

Einstein's argument:

1. Drop the altitude from the right-angle vertex `C` to the hypotenuse. Its foot `H`
   splits the right triangle `T` (legs `cA`, `cB`, hypotenuse `h`) into two smaller
   triangles `T₁` and `T₂`.
2. **Each sub-triangle is similar to `T`** (they share an angle with `T` and each has a
   right angle). In `T₁` the side corresponding to `T`'s hypotenuse is the leg `cA`; in
   `T₂` it is the leg `cB`.
3. By the area–square law, writing `k` for the shared shape constant,
   `Area(T) = k·h²`, `Area(T₁) = k·cA²`, `Area(T₂) = k·cB²`.
4. Since `H` lies inside the hypotenuse, `Area(T) = Area(T₁) + Area(T₂)`, hence
   `k·h² = k·cA² + k·cB²`, and cancelling `k` gives `h² = cA² + cB²`.

## What This File Proves (0 sorries, 0 axioms)

The file isolates Einstein's argument into three fully verified layers.

- **Layer 1 — the area–square law** (`triArea_scale`): for a triangle of base `b` and
  height `t`, scaling every length by a factor `r` scales the area by exactly `r²`. This
  is the one geometric principle Einstein relies on, proved from `Area = ½·base·height`.

- **Layer 2 — the algebraic skeleton** (`einstein_pythagorean`): *given* the three
  similar areas `k·cA²`, `k·cB²`, `k·h²` and the dissection
  `Area(T) = Area(T₁) + Area(T₂)`, cancelling the shape constant yields
  `cA² + cB² = h²`. This is the "cancel `k`" step, verified without any geometry.

- **Layer 3 — the altitude decomposition realised** (`altitudeFoot`, `foot_perp`,
  `geometric_mean_A`, `geometric_mean_B`, `segments_sum`, `altitude_geometric_mean`,
  `pythagorean_via_altitude`):
  we build the altitude foot `H` explicitly in a real inner-product space, prove it is
  perpendicular to the hypotenuse, and verify the two **leg geometric-mean relations**
  `cA² = h·|AH|` and `cB² = h·|HB|`, the **altitude geometric-mean relation**
  `|CH|² = |AH|·|HB|`, and the betweenness identity `|AH| + |HB| = h`. These are exactly
  the numerical shadows of "`T₁`, `T₂` are similar to `T`" (and to each other), and
  summing the leg relations reconstructs `h² = cA² + cB²`.

## Honesty note

Once a Euclidean model is fixed, the norm already encodes distance, so the one-line
inner-product identity `‖A-B‖² = ‖A-C‖² + ‖B-C‖²` (`pythagorean_core`) *is* Pythagoras.
Layer 3 does not pretend to be foundationally independent of that identity; its value is
that it verifies the **geometric-mean / altitude decomposition** — the metric content of
Einstein's similar-triangles picture — rather than the bare polarization identity.
Layers 1 and 2 capture the parts of Einstein's reasoning that are genuinely independent
of coordinates.

Tags: geometry, euclidean-geometry, inner-product, similar-triangles, einstein, classic
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped RealInnerProductSpace

namespace PythagoreanEinstein

-- ============================================================
-- Layer 1: The area–square law for similar triangles
-- ============================================================

/-- Area of a triangle with base `b` and height `t`. -/
noncomputable def triArea (b t : ℝ) : ℝ := b * t / 2

/-- **The one geometric principle Einstein uses.**
Scaling every linear dimension of a triangle by a factor `r` scales its area by `r²`.
This is the content of "area is proportional to the square of a linear dimension". -/
theorem triArea_scale (r b t : ℝ) : triArea (r * b) (r * t) = r ^ 2 * triArea b t := by
  unfold triArea; ring

-- ============================================================
-- Layer 2: The algebraic skeleton — "cancel the shape constant"
-- ============================================================

/-- **Einstein's argument, algebraically.**
The altitude splits the right triangle into two pieces similar to the whole. Writing `k`
for the shared shape constant (area = `k` × hypotenuse²), the three areas are `k·cA²`,
`k·cB²`, `k·h²`, and additivity of area gives `k·h² = k·cA² + k·cB²`. Cancelling the
nonzero constant `k` yields the Pythagorean relation. No coordinates are used. -/
theorem einstein_pythagorean {cA cB h k areaWhole areaA areaB : ℝ}
    (hk : k ≠ 0)
    (hWhole : areaWhole = k * h ^ 2)
    (hA : areaA = k * cA ^ 2)
    (hB : areaB = k * cB ^ 2)
    (hdissect : areaWhole = areaA + areaB) :
    cA ^ 2 + cB ^ 2 = h ^ 2 := by
  rw [hWhole, hA, hB] at hdissect
  -- hdissect : k * h ^ 2 = k * cA ^ 2 + k * cB ^ 2
  have hcancel : k * (cA ^ 2 + cB ^ 2) = k * h ^ 2 := by linear_combination -hdissect
  exact mul_left_cancel₀ hk hcancel

-- ============================================================
-- Layer 3: The altitude decomposition, realised in a Euclidean model
-- ============================================================

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The one-line inner-product identity that a Euclidean model already contains:
for a right angle at `C` (i.e. `⟪A - C, B - C⟫ = 0`), the hypotenuse squared equals the
sum of the leg squares. This is the metric form of Pythagoras. -/
theorem pythagorean_core (A B C : F) (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖A - B‖ ^ 2 = ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 := by
  have hAB : A - B = (A - C) - (B - C) := by abel
  rw [hAB, norm_sub_sq_real, hperp]
  ring

/-- The foot of the altitude dropped from the right-angle vertex `C` onto the hypotenuse
`AB`, expressed as an explicit affine combination of `A` and `B`. The parameter
`t = |CA|² / |AB|²` is the classical similar-triangle ratio. -/
noncomputable def altitudeFoot (A B C : F) : F :=
  A + (‖A - C‖ ^ 2 / ‖A - B‖ ^ 2) • (B - A)

section Altitude
variable (A B C : F) (hAB : A ≠ B)

omit [InnerProductSpace ℝ F] in
private theorem hnorm_pos (hAB : A ≠ B) : (0 : ℝ) < ‖A - B‖ ^ 2 := by
  have : A - B ≠ 0 := sub_ne_zero.mpr hAB
  positivity

omit [InnerProductSpace ℝ F] in
private theorem hnorm_ne (hAB : A ≠ B) : ‖A - B‖ ≠ 0 := by
  have : A - B ≠ 0 := sub_ne_zero.mpr hAB
  simpa using norm_ne_zero_iff.mpr this

include hAB in
/-- The altitude is perpendicular to the hypotenuse: `⟪C - H, A - B⟫ = 0`.
This is the defining property of the foot of the altitude. -/
theorem foot_perp (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ⟪C - altitudeFoot A B C, A - B⟫ = (0 : ℝ) := by
  have hpos := hnorm_pos A B hAB
  have hne2 : ‖A - B‖ ^ 2 ≠ 0 := ne_of_gt hpos
  have hne := hnorm_ne A B hAB
  set t : ℝ := ‖A - C‖ ^ 2 / ‖A - B‖ ^ 2 with ht
  have hCH : C - altitudeFoot A B C = (C - A) - t • (B - A) := by
    unfold altitudeFoot; rw [← ht]; abel
  rw [hCH, inner_sub_left, real_inner_smul_left]
  -- ⟪C - A, A - B⟫ - t * ⟪B - A, A - B⟫ = 0
  have e1 : ⟪C - A, A - B⟫ = -‖A - C‖ ^ 2 := by
    have hexp : C - A = -(A - C) := by abel
    have hAB2 : A - B = (A - C) - (B - C) := by abel
    rw [hexp, hAB2, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      show ⟪A - C, B - C⟫ = (0 : ℝ) from hperp]
    ring
  have e2 : ⟪B - A, A - B⟫ = -‖A - B‖ ^ 2 := by
    have hBA : B - A = -(A - B) := by abel
    rw [hBA, inner_neg_left, real_inner_self_eq_norm_sq]
  rw [e1, e2, ht]
  field_simp
  ring

include hAB in
/-- Distance from `A` to the foot equals `t · |AB| = |CA|²/|AB|`. -/
theorem dist_A_foot :
    ‖A - altitudeFoot A B C‖ = ‖A - C‖ ^ 2 / ‖A - B‖ := by
  have hne := hnorm_ne A B hAB
  set t : ℝ := ‖A - C‖ ^ 2 / ‖A - B‖ ^ 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hAH : A - altitudeFoot A B C = t • (A - B) := by
    unfold altitudeFoot; rw [← ht, smul_sub, smul_sub]; abel
  rw [hAH, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ht]
  field_simp

include hAB in
/-- Distance from the foot to `B` equals `(1 - t) · |AB| = |CB|²/|AB|`. -/
theorem dist_foot_B (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖altitudeFoot A B C - B‖ = ‖B - C‖ ^ 2 / ‖A - B‖ := by
  have hpos := hnorm_pos A B hAB
  have hne := hnorm_ne A B hAB
  have hcore := pythagorean_core A B C hperp
  set t : ℝ := ‖A - C‖ ^ 2 / ‖A - B‖ ^ 2 with ht
  have hle : ‖A - C‖ ^ 2 ≤ ‖A - B‖ ^ 2 := by
    rw [hcore]; nlinarith [sq_nonneg ‖B - C‖]
  have h1t : 0 ≤ 1 - t := by
    rw [ht, sub_nonneg, div_le_one hpos]; exact hle
  have h1mt : 1 - t = ‖B - C‖ ^ 2 / ‖A - B‖ ^ 2 := by
    rw [ht]; field_simp; linarith [hcore]
  have hHB : altitudeFoot A B C - B = (1 - t) • (A - B) := by
    unfold altitudeFoot; rw [← ht, sub_smul, one_smul, smul_sub, smul_sub]; abel
  rw [hHB, norm_smul, Real.norm_eq_abs, abs_of_nonneg h1t, h1mt]
  field_simp

end Altitude

section Geometric
variable (A B C : F) (hAB : A ≠ B)

include hAB in
/-- **Geometric-mean relation for leg `CA`.** `|CA|² = |AB| · |AH|`.
This is the numerical form of "sub-triangle `T₁` is similar to `T`". -/
theorem geometric_mean_A :
    ‖A - C‖ ^ 2 = ‖A - B‖ * ‖A - altitudeFoot A B C‖ := by
  have hne := hnorm_ne A B hAB
  rw [dist_A_foot A B C hAB]
  field_simp

include hAB in
/-- **Geometric-mean relation for leg `CB`.** `|CB|² = |AB| · |HB|`.
This is the numerical form of "sub-triangle `T₂` is similar to `T`". -/
theorem geometric_mean_B (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖B - C‖ ^ 2 = ‖A - B‖ * ‖altitudeFoot A B C - B‖ := by
  have hne := hnorm_ne A B hAB
  rw [dist_foot_B A B C hAB hperp]
  field_simp

include hAB in
/-- **Betweenness.** The foot lies inside the hypotenuse: `|AH| + |HB| = |AB|`.
This is the dissection `Area(T) = Area(T₁) + Area(T₂)` at the level of the base. -/
theorem segments_sum (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖A - altitudeFoot A B C‖ + ‖altitudeFoot A B C - B‖ = ‖A - B‖ := by
  have hne := hnorm_ne A B hAB
  have hcore := pythagorean_core A B C hperp
  rw [dist_A_foot A B C hAB, dist_foot_B A B C hAB hperp, ← add_div,
    div_eq_iff hne, ← hcore]
  ring

include hAB in
/-- **Pythagoras via the altitude decomposition (Einstein's route).**
Multiplying the betweenness identity by `|AB|` and substituting the two geometric-mean
relations rebuilds `|AB|² = |CA|² + |CB|²`:
`|AB|² = |AB|·(|AH| + |HB|) = |AB|·|AH| + |AB|·|HB| = |CA|² + |CB|²`. -/
theorem pythagorean_via_altitude (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 = ‖A - B‖ ^ 2 := by
  have hgA := geometric_mean_A A B C hAB
  have hgB := geometric_mean_B A B C hAB hperp
  have hsum := segments_sum A B C hAB hperp
  have key : ‖A - B‖ ^ 2
      = ‖A - B‖ * (‖A - altitudeFoot A B C‖ + ‖altitudeFoot A B C - B‖) := by
    rw [hsum]; ring
  rw [key, mul_add, ← hgA, ← hgB]

include hAB in
/-- **Geometric-mean (altitude) theorem.** The altitude from the right-angle vertex is the
geometric mean of the two hypotenuse segments it cuts: `|CH|² = |AH| · |HB|`.  This is the
third classical member of the altitude family (alongside the two leg relations
`geometric_mean_A`, `geometric_mean_B`) and the numerical form of "the two sub-triangles
`T₁`, `T₂` are similar to each other".  Proof: the altitude splits `T` into the right
sub-triangle `A H C` (right angle at the foot `H`, by `foot_perp`), so `pythagorean_core`
gives `|AC|² = |AH|² + |CH|²`; substituting `|AC|² = |AB|·|AH|` (`geometric_mean_A`) and
`|HB| = |AB| − |AH|` (`segments_sum`) collapses the difference to `|AH|·|HB|`. -/
theorem altitude_geometric_mean (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖C - altitudeFoot A B C‖ ^ 2
      = ‖A - altitudeFoot A B C‖ * ‖altitudeFoot A B C - B‖ := by
  -- The altitude segment `A - H` is parallel to the hypotenuse `A - B`.
  have hAHpar : A - altitudeFoot A B C = (‖A - C‖ ^ 2 / ‖A - B‖ ^ 2) • (A - B) := by
    unfold altitudeFoot; rw [smul_sub, smul_sub]; abel
  -- so the altitude `C - H` meets it at a right angle at the foot `H`.
  have hCHperp : ⟪C - altitudeFoot A B C, A - B⟫ = (0 : ℝ) := foot_perp A B C hAB hperp
  have hperp2 : ⟪A - altitudeFoot A B C, C - altitudeFoot A B C⟫ = (0 : ℝ) := by
    have hflip : (⟪A - B, C - altitudeFoot A B C⟫ : ℝ) = 0 := by
      rw [real_inner_comm]; exact hCHperp
    rw [hAHpar, real_inner_smul_left, hflip, mul_zero]
  -- Pythagoras on the right sub-triangle `A H C`: `|AC|² = |AH|² + |CH|²`.
  have hsub := pythagorean_core A C (altitudeFoot A B C) hperp2
  have hgA := geometric_mean_A A B C hAB          -- `|AC|² = |AB|·|AH|`
  have hsum := segments_sum A B C hAB hperp        -- `|AH| + |HB| = |AB|`
  have hCH : ‖C - altitudeFoot A B C‖ ^ 2
      = ‖A - C‖ ^ 2 - ‖A - altitudeFoot A B C‖ ^ 2 := by linarith
  have hBsub : ‖altitudeFoot A B C - B‖
      = ‖A - B‖ - ‖A - altitudeFoot A B C‖ := by linarith
  rw [hCH, hgA, hBsub]; ring

include hAB in
/-- **Altitude-on-hypotenuse length.** The altitude from the right-angle vertex has length
`|CH| = |CA|·|CB| / |AB|` — the product of the legs divided by the hypotenuse. Equivalently,
`|AB|·|CH| = |CA|·|CB|`, the statement that the triangle's area computed on the hypotenuse
(`½|AB|·|CH|`) equals its area computed on the legs (`½|CA|·|CB|`). It is the positive square
root of the altitude geometric-mean relation `|CH|² = |AH|·|HB|` after substituting the two
segment lengths `|AH| = |CA|²/|AB|` and `|HB| = |CB|²/|AB|`. -/
theorem altitude_length (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖C - altitudeFoot A B C‖ = ‖A - C‖ * ‖B - C‖ / ‖A - B‖ := by
  have hne := hnorm_ne A B hAB
  have hgm := altitude_geometric_mean A B C hAB hperp
  have hAH := dist_A_foot A B C hAB
  have hHB := dist_foot_B A B C hAB hperp
  have hlhs : 0 ≤ ‖C - altitudeFoot A B C‖ := norm_nonneg _
  have hrhs : 0 ≤ ‖A - C‖ * ‖B - C‖ / ‖A - B‖ := by positivity
  have hsq : ‖C - altitudeFoot A B C‖ ^ 2 = (‖A - C‖ * ‖B - C‖ / ‖A - B‖) ^ 2 := by
    rw [hgm, hAH, hHB]; field_simp
  rw [← Real.sqrt_sq hlhs, hsq, Real.sqrt_sq hrhs]

include hAB in
/-- **Area computed two ways agree** — the hypotenuse–leg area identity underpinning
Einstein's dissection. Computing the triangle's area with the hypotenuse as base and the
altitude `|CH|` as height, `½·|AB|·|CH|`, yields the same value as computing it from the two
perpendicular legs, `½·|CA|·|CB|`. This is exactly `altitude_length`
(`|CH| = |CA|·|CB|/|AB|`) cleared of its denominator, and it ties Layer 1's area functional
`triArea` back to the Layer 3 altitude decomposition — the "same area, two bases" fact that
makes the area–square law (`triArea_scale`) applicable to Einstein's three similar pieces. -/
theorem triArea_hypotenuse_eq_legs (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    triArea ‖A - B‖ ‖C - altitudeFoot A B C‖ = triArea ‖A - C‖ ‖B - C‖ := by
  have hne := hnorm_ne A B hAB
  unfold triArea
  rw [altitude_length A B C hAB hperp]
  field_simp

include hAB in
/-- **Einstein's key step, leg-`CA` piece: the similar sub-triangle's area scales as the
squared side ratio.**  The altitude from `C` cuts off the sub-triangle `A H C`, similar to the
whole `A B C` with ratio `|CA| / |AB|` (corresponding sides `CA ↔ AB`).  Its area is therefore
`(|CA| / |AB|)²` times the whole triangle's area:

  `Area(A H C) = (|CA|² / |AB|²) · Area(A B C)`.

Both pieces are measured with the same altitude `|CH|` as height, so the ratio of areas is the
ratio of bases `|AH| / |AB| = |CA|² / |AB|²` (`dist_A_foot`).  This is the concrete realisation
of the abstract shape-constant law `triArea_scale` on Einstein's dissection: area is
proportional to the square of a corresponding side — exactly why summing the two pieces
recovers Pythagoras. -/
theorem triArea_sub_A_ratio (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    triArea ‖A - altitudeFoot A B C‖ ‖C - altitudeFoot A B C‖
      = (‖A - C‖ ^ 2 / ‖A - B‖ ^ 2) * triArea ‖A - B‖ ‖C - altitudeFoot A B C‖ := by
  have hne := hnorm_ne A B hAB
  unfold triArea
  rw [dist_A_foot A B C hAB]
  field_simp

include hAB in
/-- **Einstein's key step, leg-`CB` piece.**  The altitude from `C` cuts off the sub-triangle
`H B C`, similar to the whole with ratio `|CB| / |AB|`; its area is `(|CB| / |AB|)²` times the
whole:

  `Area(H B C) = (|CB|² / |AB|²) · Area(A B C)`.

The `CB`-leg companion of `triArea_sub_A_ratio`, via `dist_foot_B` (`|HB| = |CB|² / |AB|`).
Adding the two squared ratios gives `(|CA|² + |CB|²)/|AB|² = 1` (`pythagorean_via_altitude`):
the two similar pieces exactly reconstitute the whole. -/
theorem triArea_sub_B_ratio (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    triArea ‖altitudeFoot A B C - B‖ ‖C - altitudeFoot A B C‖
      = (‖B - C‖ ^ 2 / ‖A - B‖ ^ 2) * triArea ‖A - B‖ ‖C - altitudeFoot A B C‖ := by
  have hne := hnorm_ne A B hAB
  unfold triArea
  rw [dist_foot_B A B C hAB hperp]
  field_simp

include hAB in
/-- **The area-level dissection: the two similar pieces reconstitute the whole.**  The altitude
from the right-angle vertex `C` splits triangle `A B C` into two sub-triangles `A H C` and
`H B C` whose areas sum to the whole:

  `Area(A H C) + Area(H B C) = Area(A B C)`.

This is Einstein's dissection at the level of area — the companion of `segments_sum` (which
states it at the level of the base `|AH| + |HB| = |AB|`).  Since all three triangles share the
altitude `|CH|` as height, area additivity is base additivity scaled by `|CH|/2`.  Together
with the two squared-ratio identities `triArea_sub_A_ratio`, `triArea_sub_B_ratio`, it is
Einstein's proof of Pythagoras: two pieces, each with area proportional to the square of its
governing leg, tile the whole. -/
theorem triArea_pieces_sum_whole (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    triArea ‖A - altitudeFoot A B C‖ ‖C - altitudeFoot A B C‖
        + triArea ‖altitudeFoot A B C - B‖ ‖C - altitudeFoot A B C‖
      = triArea ‖A - B‖ ‖C - altitudeFoot A B C‖ := by
  have hsum := segments_sum A B C hAB hperp
  unfold triArea
  rw [← hsum]
  ring

include hAB in
/-- **The inverse (reciprocal) Pythagorean theorem.**  For a right angle at `C` with
non-degenerate legs (`A ≠ C`, `B ≠ C`), the *reciprocals of the squares* of the two legs
sum to the reciprocal of the square of the altitude `|CH|` dropped onto the hypotenuse:

  `1 / |CH|²  =  1 / |CA|²  +  1 / |CB|²`.

This is the elegant "upside-down" companion of Pythagoras `|CA|² + |CB|² = |CB'|²`: whereas
Pythagoras adds the leg squares to the hypotenuse square, the inverse theorem adds their
*reciprocal* squares to the reciprocal altitude square.  It follows immediately from the two
altitude facts already proved here: `altitude_length` gives `|CH| = |CA|·|CB| / |AB|`, so
`1/|CH|² = |AB|² / (|CA|²·|CB|²)`, and `pythagorean_via_altitude` rewrites the numerator
`|AB|² = |CA|² + |CB|²`, splitting the single fraction into `1/|CB|² + 1/|CA|²`. -/
theorem inverse_pythagorean (hAC : A ≠ C) (hBC : B ≠ C)
    (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    1 / ‖C - altitudeFoot A B C‖ ^ 2
      = 1 / ‖A - C‖ ^ 2 + 1 / ‖B - C‖ ^ 2 := by
  have hcA : ‖A - C‖ ≠ 0 := by
    have : A - C ≠ 0 := sub_ne_zero.mpr hAC
    simpa using norm_ne_zero_iff.mpr this
  have hcB : ‖B - C‖ ≠ 0 := by
    have : B - C ≠ 0 := sub_ne_zero.mpr hBC
    simpa using norm_ne_zero_iff.mpr this
  have hlen := altitude_length A B C hAB hperp
  have hpy := pythagorean_via_altitude A B C hAB hperp
  have hCH2 : ‖C - altitudeFoot A B C‖ ^ 2
      = ‖A - C‖ ^ 2 * ‖B - C‖ ^ 2 / ‖A - B‖ ^ 2 := by
    rw [hlen, div_pow, mul_pow]
  rw [hCH2, ← hpy, one_div_div]
  field_simp
  ring

/-- The **inradius** of the right triangle `A B C` (right angle at `C`):
`r = (|CA| + |CB| − |AB|)/2`.  For a right triangle the inscribed-circle radius has this
classical closed form — the legs' sum minus the hypotenuse, halved. -/
noncomputable def inradius (A B C : F) : ℝ := (‖A - C‖ + ‖B - C‖ - ‖A - B‖) / 2

omit [InnerProductSpace ℝ F] in
/-- **The inradius is nonnegative.**  Immediate from the triangle inequality
`|AB| ≤ |CA| + |CB|` (writing `A - B = (A - C) - (B - C)` and applying `norm_sub_le`); no right
angle is needed. -/
theorem inradius_nonneg (A B C : F) : 0 ≤ inradius A B C := by
  unfold inradius
  have h : ‖A - B‖ ≤ ‖A - C‖ + ‖B - C‖ := by
    have hrw : A - B = (A - C) - (B - C) := by abel
    rw [hrw]; exact norm_sub_le _ _
  linarith

/-- **Area–inradius identity (`Area = r·s`), pinned to the right-triangle inradius.**
Twice the area of the right triangle (`|CA|·|CB|`) equals the inradius times the perimeter:

  `2 · Area = r · (|CA| + |CB| + |AB|)`,

i.e. `Area = r · s` with `s` the semiperimeter — the general triangle identity, here made
completely explicit because for a right angle at `C` the inradius takes the closed form
`r = (a + b − c)/2` (`inradius`).  The proof is pure algebra from `pythagorean_core`:
`(a + b − c)(a + b + c) = (a + b)² − c² = 2ab` once `c² = a² + b²`. -/
theorem two_area_eq_inradius_mul_perimeter (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    2 * triArea ‖A - C‖ ‖B - C‖
      = inradius A B C * (‖A - C‖ + ‖B - C‖ + ‖A - B‖) := by
  unfold triArea inradius
  linear_combination (1 / 2 : ℝ) * pythagorean_core A B C hperp

include hAB in
/-- **The foot divides the hypotenuse in the ratio of the squared legs.**  The altitude foot
`H` splits the hypotenuse `AB` into segments `|AH|` and `|HB|` whose lengths are proportional
to the squares of the two adjacent legs: `|AH| · |CB|² = |HB| · |CA|²`, i.e.
`|AH| / |HB| = |CA|² / |CB|²`.  This is the classical companion of the two geometric-mean
relations: the near segment `|AH|` is to the far segment `|HB|` as the square of the leg
meeting `A` (`|CA|`) is to the square of the leg meeting `B` (`|CB|`).  It follows by
cross-multiplying `geometric_mean_A` (`|CA|² = |AB|·|AH|`) and `geometric_mean_B`
(`|CB|² = |AB|·|HB|`): both sides equal `|AB|·|AH|·|HB|`. -/
theorem foot_divides_hypotenuse_sq_ratio (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖A - altitudeFoot A B C‖ * ‖B - C‖ ^ 2
      = ‖altitudeFoot A B C - B‖ * ‖A - C‖ ^ 2 := by
  have hgA := geometric_mean_A A B C hAB
  have hgB := geometric_mean_B A B C hAB hperp
  rw [hgA, hgB]; ring

include hAB in
/-- **The altitude realises the Pythagorean split from `C` to the hypotenuse line.**  For the
foot `H = altitudeFoot A B C` and *any* point `P = A + s·(B − A)` on the hypotenuse line, the
squared distance from `C` to `P` decomposes orthogonally as
`|CP|² = |CH|² + |HP|².`
Because `H − P = (t − s)·(B − A)` is parallel to the hypotenuse and `⟪C − H, A − B⟫ = 0`
(`foot_perp`), the cross term in `‖(C − H) + (H − P)‖²` vanishes.  This is the Pythagorean
theorem applied to the right sub-triangle `C H P` (right angle at the foot `H`), and it is the
engine behind the extremal property `altitude_foot_minimizes`. -/
theorem altitude_foot_dist_split (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) (s : ℝ) :
    ‖C - (A + s • (B - A))‖ ^ 2
      = ‖C - altitudeFoot A B C‖ ^ 2
        + ‖altitudeFoot A B C - (A + s • (B - A))‖ ^ 2 := by
  have hCHperp : ⟪C - altitudeFoot A B C, A - B⟫ = (0 : ℝ) := foot_perp A B C hAB hperp
  have hHP : altitudeFoot A B C - (A + s • (B - A))
      = (‖A - C‖ ^ 2 / ‖A - B‖ ^ 2 - s) • (B - A) := by
    unfold altitudeFoot; module
  have hperp2 : ⟪C - altitudeFoot A B C, altitudeFoot A B C - (A + s • (B - A))⟫ = (0 : ℝ) := by
    rw [hHP, real_inner_smul_right]
    have hBA : (B - A : F) = -(A - B) := by abel
    rw [hBA, inner_neg_right, hCHperp, neg_zero, mul_zero]
  have hsplit : C - (A + s • (B - A))
      = (C - altitudeFoot A B C) + (altitudeFoot A B C - (A + s • (B - A))) := by abel
  rw [hsplit, norm_add_sq_real, hperp2]; ring

include hAB in
/-- **The altitude is the shortest segment from `C` to the hypotenuse line.**  Among *all*
points `P = A + s·(B − A)` on the line through the hypotenuse `AB`, the foot of the altitude
`H = altitudeFoot A B C` minimises the distance to the right-angle vertex `C`:
`|CH| ≤ |CP|`  for every `s`.
This is the extremal (orthogonal-projection) characterisation of the altitude foot — the
perpendicular from a point to a line is the shortest path to it.  Immediate from the orthogonal
split `altitude_foot_dist_split`: `|CP|² = |CH|² + |HP|² ≥ |CH|²`, and both sides are
non-negative, so the same order holds for the norms themselves. -/
theorem altitude_foot_minimizes (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) (s : ℝ) :
    ‖C - altitudeFoot A B C‖ ≤ ‖C - (A + s • (B - A))‖ := by
  have hsplit := altitude_foot_dist_split A B C hAB hperp s
  have ha : (0 : ℝ) ≤ ‖C - altitudeFoot A B C‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖C - (A + s • (B - A))‖ := norm_nonneg _
  have h1 : ‖C - altitudeFoot A B C‖ ^ 2 ≤ ‖C - (A + s • (B - A))‖ ^ 2 := by
    rw [hsplit]; nlinarith [sq_nonneg ‖altitudeFoot A B C - (A + s • (B - A))‖]
  calc ‖C - altitudeFoot A B C‖
      = Real.sqrt (‖C - altitudeFoot A B C‖ ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (‖C - (A + s • (B - A))‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = ‖C - (A + s • (B - A))‖ := Real.sqrt_sq hb

end Geometric

-- ============================================================
-- Capstone: the two routes agree
-- ============================================================

/-- The altitude route reproduces the metric Pythagorean identity (`pythagorean_core`),
confirming Einstein's similar-triangles decomposition is faithful. -/
theorem einstein_matches_core (A B C : F) (hAB : A ≠ B)
    (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 = ‖A - B‖ ^ 2 ∧
    ‖A - B‖ ^ 2 = ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 :=
  ⟨pythagorean_via_altitude A B C hAB hperp, pythagorean_core A B C hperp⟩

-- ============================================================
-- Euclid VI.31: the generalized Pythagorean theorem
-- ============================================================

/-- **Euclid VI.31 — the generalized Pythagorean theorem.**  For a right angle at `C`, erect
*similar* figures of one common shape on the three sides.  By similarity the area of a figure
of fixed shape spanned on a segment of length `s` is `figArea s = shapeConst · s²` — area scales
as the *square* of the linear dimension — so the entire shape is encoded in the single constant
`shapeConst`.  Then the figure on the hypotenuse has area equal to the sum of the areas of the
figures on the two legs:

`figArea ‖A − B‖ = figArea ‖A − C‖ + figArea ‖B − C‖.`

Pythagoras is the special case of squares (`shapeConst = 1`); Euclid's Proposition VI.31 allows
semicircles (below), similar triangles, regular polygons, or any fixed shape.  The proof is
immediate from `pythagorean_core` together with the degree-2 homogeneity `hfig`: pulling the
common constant out reduces the three-figure identity to the metric Pythagorean identity. -/
theorem euclid_VI_31 (figArea : ℝ → ℝ) (shapeConst : ℝ)
    (hfig : ∀ s : ℝ, figArea s = shapeConst * s ^ 2)
    (A B C : F) (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    figArea ‖A - B‖ = figArea ‖A - C‖ + figArea ‖B - C‖ := by
  simp only [hfig]
  rw [pythagorean_core A B C hperp]; ring

/-- **Semicircles on the three sides — a concrete instance of Euclid VI.31.**  The semicircle
erected on a segment of length `s` (taken as diameter) has area `π s² / 8` (half of `π (s/2)²`).
Feeding this shape functional to `euclid_VI_31` gives that the semicircle on the hypotenuse has
area equal to the sum of the semicircles on the two legs — the additivity identity underlying
Hippocrates' quadrature of the lunes. -/
theorem semicircles_on_sides (A B C : F) (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    Real.pi * ‖A - B‖ ^ 2 / 8
      = Real.pi * ‖A - C‖ ^ 2 / 8 + Real.pi * ‖B - C‖ ^ 2 / 8 := by
  have h := euclid_VI_31 (fun s => Real.pi * s ^ 2 / 8) (Real.pi / 8)
    (fun s => by ring) A B C hperp
  simpa using h

/-- **Hippocrates' quadrature of the lunes.**  Erect a semicircle outward on each *leg*
(diameters `CA`, `CB`) and the semicircle on the hypotenuse `AB` on the side of the triangle —
by Thales the latter passes through the right-angle vertex `C`, so it decomposes into the
triangle `ABC` plus the two circular *segments* cut off by the chords `CA` and `CB`:

`(area of semicircle on AB)  =  (area of triangle ABC)  +  segA  +  segB`   (`hbig`).

Each **lune** is the sliver between a leg-semicircle and the hypotenuse-semicircle, i.e.
`luneA = (semicircle on CA) − segA` and `luneB = (semicircle on CB) − segB`.  Hippocrates'
celebrated theorem (c. 440 BC — the first rigorous quadrature of a curvilinear region) is that
the two lunes together have the **rectilinear** area of the triangle:

`luneA + luneB  =  area of triangle ABC.`

The proof is the algebraic heart of the classical argument: by `semicircles_on_sides` the two
leg-semicircles sum to the hypotenuse-semicircle, so
`luneA + luneB = (semiCA + semiCB) − segA − segB = semiAB − segA − segB = triArea` by `hbig`.
Only this decomposition `hbig` carries geometric content (the Thales inscription of `C`); the
quadrature identity itself is forced by the Pythagorean additivity of the semicircles. -/
theorem hippocrates_lunes (A B C : F) (hperp : ⟪A - C, B - C⟫ = (0 : ℝ))
    (triArea segA segB : ℝ)
    (hbig : Real.pi * ‖A - B‖ ^ 2 / 8 = triArea + segA + segB) :
    (Real.pi * ‖A - C‖ ^ 2 / 8 - segA) + (Real.pi * ‖B - C‖ ^ 2 / 8 - segB) = triArea := by
  have hsemi := semicircles_on_sides A B C hperp
  linarith

/-- **Thales' theorem / the circumradius of a right triangle.** The right-angle vertex `C`
lies on the circle whose diameter is the hypotenuse `AB`: the hypotenuse midpoint
`M = A + ½·(B − A)` is at distance exactly `‖A − B‖ / 2` from `C`. Equivalently, the
circumradius of a right triangle is half its hypotenuse. This is precisely the inscription of
`C` in the hypotenuse semicircle that `hippocrates_lunes` invokes ("by Thales the latter passes
through the right-angle vertex `C`") but does not itself prove. The proof writes
`M − C = ½·((A−C)+(B−C))` and evaluates
`‖(A−C)+(B−C)‖² = ‖A−C‖² + 2⟪A−C,B−C⟫ + ‖B−C‖² = ‖A−C‖² + ‖B−C‖² = ‖A−B‖²`, using the right
angle (`hperp`) and `pythagorean_core`. -/
theorem thales_circumradius (A B C : F) (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖(A + (2⁻¹ : ℝ) • (B - A)) - C‖ = ‖A - B‖ / 2 := by
  have hsum_sq : ‖(A - C) + (B - C)‖ ^ 2 = ‖A - B‖ ^ 2 := by
    rw [norm_add_sq_real, hperp]
    have hp := pythagorean_core A B C hperp
    linarith
  have hsum : ‖(A - C) + (B - C)‖ = ‖A - B‖ := by
    have h1 := norm_nonneg ((A - C) + (B - C))
    have h2 := norm_nonneg (A - B)
    nlinarith [hsum_sq, h1, h2]
  have hdecomp : (A + (2⁻¹ : ℝ) • (B - A)) - C = (2⁻¹ : ℝ) • ((A - C) + (B - C)) := by
    module
  rw [hdecomp, norm_smul, hsum, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
  ring

/-- **The hypotenuse midpoint is the circumcenter of the right triangle.** All three vertices
lie at the same distance `‖A − B‖ / 2` from the hypotenuse midpoint `M = A + ½·(B − A)`: the two
hypotenuse endpoints trivially (`M` is their midpoint), and the right-angle vertex `C` by
`thales_circumradius`. So the circumcircle of a right triangle is centred at the hypotenuse
midpoint with radius half the hypotenuse — the converse-of-Thales companion of
`thales_circumradius`. -/
theorem hypotenuse_midpoint_circumcenter (A B C : F) (hperp : ⟪A - C, B - C⟫ = (0 : ℝ)) :
    ‖(A + (2⁻¹ : ℝ) • (B - A)) - A‖ = ‖A - B‖ / 2 ∧
      ‖(A + (2⁻¹ : ℝ) • (B - A)) - B‖ = ‖A - B‖ / 2 ∧
      ‖(A + (2⁻¹ : ℝ) • (B - A)) - C‖ = ‖A - B‖ / 2 := by
  refine ⟨?_, ?_, thales_circumradius A B C hperp⟩
  · have hd : (A + (2⁻¹ : ℝ) • (B - A)) - A = (2⁻¹ : ℝ) • (B - A) := by module
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹),
      norm_sub_rev B A]
    ring
  · have hd : (A + (2⁻¹ : ℝ) • (B - A)) - B = (2⁻¹ : ℝ) • (A - B) := by module
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
    ring

-- ============================================================
-- Converses: recovering the right angle from the metric data
-- ============================================================

/-- **Converse of the (metric) Pythagorean theorem.**  The forward direction
`pythagorean_core` shows a right angle at `C` forces `‖A−B‖² = ‖A−C‖² + ‖B−C‖²`.  This is the
converse: *whenever* the hypotenuse square equals the sum of the leg squares, the angle at `C`
must be right (`⟪A−C, B−C⟫ = 0`).  Expanding `‖A−B‖² = ‖(A−C)−(B−C)‖²
= ‖A−C‖² − 2⟪A−C,B−C⟫ + ‖B−C‖²` and comparing with the hypothesis leaves `2⟪A−C,B−C⟫ = 0`.
Together with `pythagorean_core` this makes the right angle *equivalent* to the numerical
Pythagorean relation (`pythagorean_core_iff`). -/
theorem pythagorean_core_converse (A B C : F)
    (h : ‖A - B‖ ^ 2 = ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2) :
    ⟪A - C, B - C⟫ = (0 : ℝ) := by
  have hR : ‖A - B‖ ^ 2
      = ‖A - C‖ ^ 2 - 2 * ⟪A - C, B - C⟫ + ‖B - C‖ ^ 2 := by
    have hAB : A - B = (A - C) - (B - C) := by abel
    rw [hAB]; exact norm_sub_sq_real _ _
  rw [hR] at h
  linarith

/-- **Pythagoras characterises the right angle.**  Combining `pythagorean_core` with its
converse: the angle at `C` is right iff the metric Pythagorean identity holds. -/
theorem pythagorean_core_iff (A B C : F) :
    ⟪A - C, B - C⟫ = (0 : ℝ) ↔ ‖A - B‖ ^ 2 = ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 :=
  ⟨pythagorean_core A B C, pythagorean_core_converse A B C⟩

/-- **The law of cosines (inner-product form).**  For *any* three points `A, B, C` — no right
angle assumed — the squared side opposite `C` equals the sum of the squared legs minus twice the
inner product at `C`:
`‖A − B‖² = ‖A − C‖² + ‖B − C‖² − 2⟪A − C, B − C⟫`.
Since `⟪A − C, B − C⟫ = ‖A − C‖·‖B − C‖·cos γ` with `γ` the angle at `C`, this is exactly the
classical law of cosines `c² = a² + b² − 2ab·cos γ`, and `pythagorean_core` is precisely its
`γ = 90°` (`⟪⟫ = 0`) special case.  Because the inner product enters *linearly*, both
`pythagorean_core` and `pythagorean_core_converse` are one-line corollaries. -/
theorem law_of_cosines (A B C : F) :
    ‖A - B‖ ^ 2 = ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 - 2 * ⟪A - C, B - C⟫ := by
  have hAB : A - B = (A - C) - (B - C) := by abel
  rw [hAB, norm_sub_sq_real]; ring

/-- **Apollonius' theorem (the median-length formula).**  For *any* triangle `A B C` — no right
angle assumed — the two sides meeting at `C` and the median `C M` to the midpoint
`M = A + ½·(B − A)` of the opposite side are related by
`|CA|² + |CB|² = 2·|CM|² + ½·|AB|².`
Writing `A − C = (M − C) + ½·(A − B)` and `B − C = (M − C) − ½·(A − B)` and adding the two
`norm_add/sub_sq_real` expansions, the cross terms `±2⟪M − C, A − B⟫` cancel, leaving twice the
median square plus half the base square.  In the right-angled case the median to the hypotenuse
has length `|CM| = ½|AB|` (`thales_circumradius`), and substituting collapses Apollonius back to
Pythagoras `|CA|² + |CB|² = |AB|²`. -/
theorem median_apollonius (A B C : F) :
    ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2
      = 2 * ‖(A + (2⁻¹ : ℝ) • (B - A)) - C‖ ^ 2 + ‖A - B‖ ^ 2 / 2 := by
  set M : F := A + (2⁻¹ : ℝ) • (B - A) with hM
  have hAC : A - C = (M - C) + (2⁻¹ : ℝ) • (A - B) := by rw [hM]; module
  have hBC : B - C = (M - C) - (2⁻¹ : ℝ) • (A - B) := by rw [hM]; module
  -- Expand each compound norm explicitly so the rewrites target the sum/difference
  -- terms and never the bare `‖M - C‖` (which `norm_sub_sq_real` would otherwise grab).
  have e1 := norm_add_sq_real (M - C) ((2⁻¹ : ℝ) • (A - B))
  have e2 := norm_sub_sq_real (M - C) ((2⁻¹ : ℝ) • (A - B))
  have hy : ‖(2⁻¹ : ℝ) • (A - B)‖ ^ 2 = ‖A - B‖ ^ 2 / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; ring
  rw [hAC, hBC, e1, e2, hy]; ring

/-- **Stewart's theorem (the cevian-length formula).**  Generalizes `median_apollonius` from
the *median* to an *arbitrary* cevian.  For any triangle `A B C` and any `t : ℝ`, let
`D = A + t·(B − A)` be the point dividing `AB` in ratio `t : (1 − t)` and drop the cevian `C D`.
Then
`(1 − t)·|CA|² + t·|CB|² = t(1 − t)·|AB|² + |CD|².`

Writing `A − C = (D − C) + t·(A − B)` and `B − C = (D − C) − (1 − t)·(A − B)`, weighting the two
`norm_add/sub_sq_real` expansions by `(1 − t)` and `t` makes the cross terms
`±2t(1 − t)⟪D − C, A − B⟫` cancel — exactly the mechanism behind Apollonius — and the leg-square
coefficients collapse to `t(1 − t)|AB|²`.

Multiplying through by `c = |AB|` and writing the signed sub-lengths `m = |AD| = t·c`,
`n = |DB| = (1 − t)·c` recovers the classical school-geometry form
`b²·n + a²·m = c·(d² + m·n)` (with `a = |CB|`, `b = |CA|`, `d = |CD|`).  The median case `t = ½`
reproduces `median_apollonius` (`|CA|² + |CB|² = 2|CM|² + ½|AB|²`); the endpoint cases `t = 0, 1`
degenerate to `D = A` / `D = B` (`|CD| = |CA|` / `|CB|`). -/
theorem stewart_cevian (A B C : F) (t : ℝ) :
    (1 - t) * ‖A - C‖ ^ 2 + t * ‖B - C‖ ^ 2
      = t * (1 - t) * ‖A - B‖ ^ 2 + ‖(A + t • (B - A)) - C‖ ^ 2 := by
  set D : F := A + t • (B - A) with hD
  have hAC : A - C = (D - C) + t • (A - B) := by rw [hD]; module
  have hBC : B - C = (D - C) - (1 - t) • (A - B) := by rw [hD]; module
  have e1 := norm_add_sq_real (D - C) (t • (A - B))
  have e2 := norm_sub_sq_real (D - C) ((1 - t) • (A - B))
  have hn1 : ‖t • (A - B)‖ ^ 2 = t ^ 2 * ‖A - B‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hn2 : ‖(1 - t) • (A - B)‖ ^ 2 = (1 - t) ^ 2 * ‖A - B‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hi1 : ⟪D - C, t • (A - B)⟫ = t * ⟪D - C, A - B⟫ := real_inner_smul_right _ _ _
  have hi2 : ⟪D - C, (1 - t) • (A - B)⟫ = (1 - t) * ⟪D - C, A - B⟫ :=
    real_inner_smul_right _ _ _
  rw [hAC, hBC, e1, e2, hn1, hn2, hi1, hi2]; ring

/-- **Acute angle ⇔ sub-Pythagorean.**  Generalizing `pythagorean_core_iff` to the acute case:
the angle at `C` is acute (`⟪A − C, B − C⟫ > 0`) iff the side opposite `C` is *shorter* than the
Pythagorean value, i.e. `‖A − B‖² < ‖A − C‖² + ‖B − C‖²`.  Immediate from `law_of_cosines`. -/
theorem pythagorean_acute_iff (A B C : F) :
    0 < ⟪A - C, B - C⟫ ↔ ‖A - B‖ ^ 2 < ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 := by
  rw [law_of_cosines A B C]; constructor <;> intro h <;> linarith

/-- **Obtuse angle ⇔ super-Pythagorean.**  The angle at `C` is obtuse (`⟪A − C, B − C⟫ < 0`) iff
the side opposite `C` is *longer* than the Pythagorean value,
`‖A − C‖² + ‖B − C‖² < ‖A − B‖²`.  Together with `pythagorean_core_iff` (right angle ⇔ equality)
and `pythagorean_acute_iff`, this completes the right/acute/obtuse trichotomy that the law of
cosines governs. -/
theorem pythagorean_obtuse_iff (A B C : F) :
    ⟪A - C, B - C⟫ < 0 ↔ ‖A - C‖ ^ 2 + ‖B - C‖ ^ 2 < ‖A - B‖ ^ 2 := by
  rw [law_of_cosines A B C]; constructor <;> intro h <;> linarith

/-- **Converse of Thales' theorem.**  `thales_circumradius` shows the right-angle vertex lies on
the circle with diameter `AB` (distance exactly `‖A−B‖/2` from the hypotenuse midpoint
`M = A + ½·(B−A)`).  This is the converse — the classical statement that *any* point `C` on that
circle sees the diameter at a right angle: if `‖M − C‖ = ‖A−B‖/2` then `⟪A−C, B−C⟫ = 0`.
Writing `M − C = ½·((A−C)+(B−C))`, the hypothesis says `‖(A−C)+(B−C)‖ = ‖A−B‖`; squaring and
expanding both sides (via `norm_add_sq_real` on the left, `norm_sub_sq_real` on the right,
since `A−B = (A−C)−(B−C)`) cancels the common leg-square terms and forces `4⟪A−C,B−C⟫ = 0`.
This is exactly the inscription of `C` in the hypotenuse semicircle that `hippocrates_lunes`
invokes but did not prove in that direction. -/
theorem thales_converse (A B C : F)
    (h : ‖(A + (2⁻¹ : ℝ) • (B - A)) - C‖ = ‖A - B‖ / 2) :
    ⟪A - C, B - C⟫ = (0 : ℝ) := by
  have hdecomp : (A + (2⁻¹ : ℝ) • (B - A)) - C = (2⁻¹ : ℝ) • ((A - C) + (B - C)) := by module
  rw [hdecomp, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)] at h
  have hnorm : ‖(A - C) + (B - C)‖ = ‖A - B‖ := by linarith
  have hsq : ‖(A - C) + (B - C)‖ ^ 2 = ‖A - B‖ ^ 2 := by rw [hnorm]
  -- Expand each side explicitly (avoids `norm_sub_sq_real` mis-firing on `‖A−C‖²`).
  have hL : ‖(A - C) + (B - C)‖ ^ 2
      = ‖A - C‖ ^ 2 + 2 * ⟪A - C, B - C⟫ + ‖B - C‖ ^ 2 := norm_add_sq_real _ _
  have hR : ‖A - B‖ ^ 2
      = ‖A - C‖ ^ 2 - 2 * ⟪A - C, B - C⟫ + ‖B - C‖ ^ 2 := by
    have hAB : A - B = (A - C) - (B - C) := by abel
    rw [hAB]; exact norm_sub_sq_real _ _
  rw [hL, hR] at hsq
  linarith

/-- **Thales characterises the right angle.**  Combining `thales_circumradius` with its
converse: the angle at `C` is right iff `C` lies on the circle with diameter `AB` (the
hypotenuse midpoint is equidistant, at `‖A−B‖/2`, from `C`). -/
theorem thales_iff (A B C : F) :
    ⟪A - C, B - C⟫ = (0 : ℝ) ↔ ‖(A + (2⁻¹ : ℝ) • (B - A)) - C‖ = ‖A - B‖ / 2 :=
  ⟨thales_circumradius A B C, thales_converse A B C⟩

#check @einstein_pythagorean
#check @pythagorean_via_altitude
#check @geometric_mean_A
#check @triArea_scale

end PythagoreanEinstein

