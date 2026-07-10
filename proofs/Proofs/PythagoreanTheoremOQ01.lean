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
    rw [hAHpar, real_inner_smul_left,
        real_inner_comm (A - B) (C - altitudeFoot A B C), hCHperp, mul_zero]
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
    rw [hgm, hAH, hHB]; field_simp; ring
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
  ring

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

#check @einstein_pythagorean
#check @pythagorean_via_altitude
#check @geometric_mean_A
#check @triArea_scale

end PythagoreanEinstein
