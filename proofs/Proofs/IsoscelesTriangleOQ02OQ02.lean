import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Isosceles triangle OQ-02-OQ-02: the law of sines in hyperbolic and spherical geometry

The parent entry (`isosceles-triangle-oq-02`) proves **Pons Asinorum** in spherical and
hyperbolic geometry, and its converse (`isosceles-triangle-oq-02-oq-01`) proves the converse,
both working purely from the *laws of cosines* with no inner product space. Both list as an
open question:

> *Derive the spherical and hyperbolic laws of sines in the same coordinate-free framework and
> combine them with these results toward a full non-Euclidean triangle-congruence toolkit.*

This file does so. As in the sibling entries, we take the (ordinary) **law of cosines** as the
only input — no inner product space, no coordinates. The two laws of cosines are

* spherical:   `cos a = cos b · cos c + sin b · sin c · cos A`,
* hyperbolic:  `cosh a = cosh b · cosh c − sinh b · sinh c · cos A`,

where `A` is the angle opposite side `a`. From either one we solve for `cos A` and compute
`sin² A = 1 − cos² A`. The key algebraic miracle is that the resulting product

* spherical:   `(sin A · sin b · sin c)²`,
* hyperbolic:  `(sin A · sinh b · sinh c)²`,

equals a **fully symmetric** function of the three sides — the *sine discriminant*

* spherical:   `Δ = 1 − cos²a − cos²b − cos²c + 2·cos a·cos b·cos c`,
* hyperbolic:  `Δ = 1 − cosh²a − cosh²b − cosh²c + 2·cosh a·cosh b·cosh c`,

which is manifestly invariant under permuting `a, b, c`. Comparing the expressions coming from
angle `A` and angle `B` and cancelling the common factor gives the **law of sines**:

* spherical:   `sin A / sin a = sin B / sin b`,
* hyperbolic:  `sin A / sinh a = sin B / sinh b`.

The two derivations are *identical* line for line — only `cos ↔ cosh`, `sin ↔ sinh` on the sides
change. This is exactly the "same coordinate-free framework" the open question asks for.

## Main results

* `sphSineDisc` / `hypSineDisc` : the symmetric sine discriminant `Δ`.
* `sphSineDisc_symm_ab` / `hypSineDisc_symm_ab` : `Δ` is symmetric in the sides.
* `sph_sinSq_eq_disc` / `hyp_sinSq_eq_disc` : `(sin A · sin b · sin c)² = Δ` (the core identity).
* `sph_law_of_sines_sq` / `hyp_law_of_sines_sq` : squared law of sines
  `(sin A · sin b)² = (sin B · sin a)²`.
* `sph_law_of_sines` / `hyp_law_of_sines` : the law of sines `sin A / sin a = sin B / sin b`
  (resp. `sin A / sinh a = sin B / sinh b`) under the usual positivity ranges.

No inner product space and no axioms are used.
-/

namespace IsoscelesTriangleOQ02OQ02

open Real Set

/-! ## Spherical geometry -/

/-- The **spherical sine discriminant**
    `Δ = 1 − cos²a − cos²b − cos²c + 2·cos a·cos b·cos c`.
    This is the symmetric quantity that the law of sines makes visible: it equals
    `(sin A · sin b · sin c)²` no matter which angle `A` we start from. -/
noncomputable def sphSineDisc (a b c : ℝ) : ℝ :=
  1 - cos a ^ 2 - cos b ^ 2 - cos c ^ 2 + 2 * cos a * cos b * cos c

/-- The spherical sine discriminant is symmetric under swapping the first two sides. -/
theorem sphSineDisc_symm_ab (a b c : ℝ) : sphSineDisc a b c = sphSineDisc b a c := by
  unfold sphSineDisc; ring

/-- The spherical sine discriminant is symmetric under swapping the last two sides. -/
theorem sphSineDisc_symm_bc (a b c : ℝ) : sphSineDisc a b c = sphSineDisc a c b := by
  unfold sphSineDisc; ring

/-- **Core identity (spherical).** From the spherical law of cosines
    `cos a = cos b · cos c + sin b · sin c · cos A`, the quantity `(sin A · sin b · sin c)²`
    equals the symmetric sine discriminant `Δ(a, b, c)`.

    The proof uses only the Pythagorean identity `sin² + cos² = 1` on `A`, `b`, `c` and the law
    of cosines; no division is required, so no nonvanishing hypotheses are needed. -/
theorem sph_sinSq_eq_disc {a b c A : ℝ}
    (hA : cos a = cos b * cos c + sin b * sin c * cos A) :
    (sin A * sin b * sin c) ^ 2 = sphSineDisc a b c := by
  have pA : sin A ^ 2 = 1 - cos A ^ 2 := by
    have := sin_sq_add_cos_sq A; linarith
  have pb : sin b ^ 2 = 1 - cos b ^ 2 := by
    have := sin_sq_add_cos_sq b; linarith
  have pc : sin c ^ 2 = 1 - cos c ^ 2 := by
    have := sin_sq_add_cos_sq c; linarith
  -- The law of cosines gives `sin b · sin c · cos A = cos a − cos b · cos c`; squaring and
  -- using `sin² = 1 − cos²` turns `(sin A sin b sin c)²` into the symmetric discriminant.
  have hcosA : sin b * sin c * cos A = cos a - cos b * cos c := by linarith
  have hsq : (sin b * sin c * cos A) ^ 2 = (cos a - cos b * cos c) ^ 2 := by rw [hcosA]
  calc (sin A * sin b * sin c) ^ 2
      = sin b ^ 2 * sin c ^ 2 * sin A ^ 2 := by ring
    _ = sin b ^ 2 * sin c ^ 2 * (1 - cos A ^ 2) := by rw [pA]
    _ = sin b ^ 2 * sin c ^ 2 - (sin b * sin c * cos A) ^ 2 := by ring
    _ = sin b ^ 2 * sin c ^ 2 - (cos a - cos b * cos c) ^ 2 := by rw [hsq]
    _ = (1 - cos b ^ 2) * (1 - cos c ^ 2) - (cos a - cos b * cos c) ^ 2 := by rw [pb, pc]
    _ = sphSineDisc a b c := by unfold sphSineDisc; ring

/-- **Squared law of sines (spherical).** From the spherical laws of cosines for angles `A`
    and `B` (opposite sides `a` and `b`), the products `sin A · sin b` and `sin B · sin a`
    have equal squares — provided the third side has `sin c ≠ 0`, so the common factor
    `sin² c` can be cancelled. -/
theorem sph_law_of_sines_sq {a b c A B : ℝ}
    (hA : cos a = cos b * cos c + sin b * sin c * cos A)
    (hB : cos b = cos a * cos c + sin a * sin c * cos B)
    (hc : sin c ≠ 0) :
    (sin A * sin b) ^ 2 = (sin B * sin a) ^ 2 := by
  have eA : (sin A * sin b * sin c) ^ 2 = sphSineDisc a b c := sph_sinSq_eq_disc hA
  have eB : (sin B * sin a * sin c) ^ 2 = sphSineDisc b a c := sph_sinSq_eq_disc hB
  rw [← sphSineDisc_symm_ab] at eB
  -- both equal `Δ(a,b,c)`; strip the common `sin² c`.
  have hc2 : sin c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have : (sin A * sin b) ^ 2 * sin c ^ 2 = (sin B * sin a) ^ 2 * sin c ^ 2 := by
    have e : (sin A * sin b) ^ 2 * sin c ^ 2 = (sin A * sin b * sin c) ^ 2 := by ring
    have e' : (sin B * sin a) ^ 2 * sin c ^ 2 = (sin B * sin a * sin c) ^ 2 := by ring
    rw [e, e', eA, eB]
  exact mul_right_cancel₀ hc2 this

/-- **Law of sines, spherical geometry.** In a spherical triangle whose sides `a, b` and angles
    `A, B, C` satisfy the laws of cosines, with all relevant sines positive (the standard range
    `0 < ·, · < π` for sides and angles), the ratios of angle-sine to opposite-side-sine agree:
    `sin A / sin a = sin B / sin b`. No inner product space is used. -/
theorem sph_law_of_sines {a b c A B : ℝ}
    (hA : cos a = cos b * cos c + sin b * sin c * cos A)
    (hB : cos b = cos a * cos c + sin a * sin c * cos B)
    (ha : 0 < sin a) (hb : 0 < sin b) (hc : 0 < sin c)
    (hA' : 0 < sin A) (hB' : 0 < sin B) :
    sin A / sin a = sin B / sin b := by
  have hsq : (sin A * sin b) ^ 2 = (sin B * sin a) ^ 2 :=
    sph_law_of_sines_sq hA hB (ne_of_gt hc)
  -- both bases positive, so equal squares give equal values, then divide.
  have hpos1 : 0 < sin A * sin b := mul_pos hA' hb
  have hpos2 : 0 < sin B * sin a := mul_pos hB' ha
  have heq : sin A * sin b = sin B * sin a := by
    nlinarith [hsq, hpos1, hpos2, sq_nonneg (sin A * sin b - sin B * sin a)]
  rw [div_eq_div_iff ha.ne' hb.ne']
  linarith [heq]

/-! ## Hyperbolic geometry

The derivation is line-for-line identical to the spherical one, with `cos ↔ cosh` and
`sin ↔ sinh` on the *sides* (angles stay ordinary `cos`/`sin`). The discriminant flips the sign
convention through `sinh² = cosh² − 1`, but comes out with the same symmetric shape. -/

/-- The **hyperbolic sine discriminant**
    `Δ = 1 − cosh²a − cosh²b − cosh²c + 2·cosh a·cosh b·cosh c`. -/
noncomputable def hypSineDisc (a b c : ℝ) : ℝ :=
  1 - cosh a ^ 2 - cosh b ^ 2 - cosh c ^ 2 + 2 * cosh a * cosh b * cosh c

/-- The hyperbolic sine discriminant is symmetric under swapping the first two sides. -/
theorem hypSineDisc_symm_ab (a b c : ℝ) : hypSineDisc a b c = hypSineDisc b a c := by
  unfold hypSineDisc; ring

/-- The hyperbolic sine discriminant is symmetric under swapping the last two sides. -/
theorem hypSineDisc_symm_bc (a b c : ℝ) : hypSineDisc a b c = hypSineDisc a c b := by
  unfold hypSineDisc; ring

/-- **Core identity (hyperbolic).** From the hyperbolic law of cosines
    `cosh a = cosh b · cosh c − sinh b · sinh c · cos A`, the quantity
    `(sin A · sinh b · sinh c)²` equals the symmetric hyperbolic sine discriminant `Δ(a, b, c)`.

    Uses `sin² A = 1 − cos² A` for the angle and `sinh² = cosh² − 1` for the sides. -/
theorem hyp_sinSq_eq_disc {a b c A : ℝ}
    (hA : cosh a = cosh b * cosh c - sinh b * sinh c * cos A) :
    (sin A * sinh b * sinh c) ^ 2 = hypSineDisc a b c := by
  have pA : sin A ^ 2 = 1 - cos A ^ 2 := by
    have := sin_sq_add_cos_sq A; linarith
  have pb : sinh b ^ 2 = cosh b ^ 2 - 1 := by
    have := cosh_sq_sub_sinh_sq b; linarith
  have pc : sinh c ^ 2 = cosh c ^ 2 - 1 := by
    have := cosh_sq_sub_sinh_sq c; linarith
  have hcosA : sinh b * sinh c * cos A = cosh b * cosh c - cosh a := by linarith
  have hsq : (sinh b * sinh c * cos A) ^ 2 = (cosh b * cosh c - cosh a) ^ 2 := by rw [hcosA]
  calc (sin A * sinh b * sinh c) ^ 2
      = sinh b ^ 2 * sinh c ^ 2 * sin A ^ 2 := by ring
    _ = sinh b ^ 2 * sinh c ^ 2 * (1 - cos A ^ 2) := by rw [pA]
    _ = sinh b ^ 2 * sinh c ^ 2 - (sinh b * sinh c * cos A) ^ 2 := by ring
    _ = sinh b ^ 2 * sinh c ^ 2 - (cosh b * cosh c - cosh a) ^ 2 := by rw [hsq]
    _ = (cosh b ^ 2 - 1) * (cosh c ^ 2 - 1) - (cosh b * cosh c - cosh a) ^ 2 := by rw [pb, pc]
    _ = hypSineDisc a b c := by unfold hypSineDisc; ring

/-- **Squared law of sines (hyperbolic).** Analogue of `sph_law_of_sines_sq`, cancelling the
    common factor `sinh² c` (needs `sinh c ≠ 0`, i.e. `c ≠ 0`). -/
theorem hyp_law_of_sines_sq {a b c A B : ℝ}
    (hA : cosh a = cosh b * cosh c - sinh b * sinh c * cos A)
    (hB : cosh b = cosh a * cosh c - sinh a * sinh c * cos B)
    (hc : sinh c ≠ 0) :
    (sin A * sinh b) ^ 2 = (sin B * sinh a) ^ 2 := by
  have eA : (sin A * sinh b * sinh c) ^ 2 = hypSineDisc a b c := hyp_sinSq_eq_disc hA
  have eB : (sin B * sinh a * sinh c) ^ 2 = hypSineDisc b a c := hyp_sinSq_eq_disc hB
  rw [← hypSineDisc_symm_ab] at eB
  have hc2 : sinh c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have : (sin A * sinh b) ^ 2 * sinh c ^ 2 = (sin B * sinh a) ^ 2 * sinh c ^ 2 := by
    have e : (sin A * sinh b) ^ 2 * sinh c ^ 2 = (sin A * sinh b * sinh c) ^ 2 := by ring
    have e' : (sin B * sinh a) ^ 2 * sinh c ^ 2 = (sin B * sinh a * sinh c) ^ 2 := by ring
    rw [e, e', eA, eB]
  exact mul_right_cancel₀ hc2 this

/-- **Law of sines, hyperbolic geometry.** In a hyperbolic triangle whose sides `a, b` and
    angles `A, B` satisfy the hyperbolic laws of cosines, with positive side-`sinh`s (`a,b,c > 0`)
    and positive angle-`sin`s, `sin A / sinh a = sin B / sinh b`. No inner product space is used. -/
theorem hyp_law_of_sines {a b c A B : ℝ}
    (hA : cosh a = cosh b * cosh c - sinh b * sinh c * cos A)
    (hB : cosh b = cosh a * cosh c - sinh a * sinh c * cos B)
    (ha : 0 < sinh a) (hb : 0 < sinh b) (hc : 0 < sinh c)
    (hA' : 0 < sin A) (hB' : 0 < sin B) :
    sin A / sinh a = sin B / sinh b := by
  have hsq : (sin A * sinh b) ^ 2 = (sin B * sinh a) ^ 2 :=
    hyp_law_of_sines_sq hA hB (ne_of_gt hc)
  have hpos1 : 0 < sin A * sinh b := mul_pos hA' hb
  have hpos2 : 0 < sin B * sinh a := mul_pos hB' ha
  have heq : sin A * sinh b = sin B * sinh a := by
    nlinarith [hsq, hpos1, hpos2, sq_nonneg (sin A * sinh b - sin B * sinh a)]
  rw [div_eq_div_iff ha.ne' hb.ne']
  linarith [heq]

end IsoscelesTriangleOQ02OQ02
