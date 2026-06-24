import Mathlib
import Proofs.CarnotTheorem

/-
# Carnot's Theorem — the metric signed-distance form with an explicit circumcenter

The parent files work entirely in the *angle* form.  `CarnotTheorem.lean`
proves

  `cos A + cos B + cos C = 1 + 4 sin(A/2) sin(B/2) sin(C/2)`,

and `CarnotTheoremOQ01OQ01.lean` pins down the range of that cosine sum.  Both
live in a bespoke trigonometric encoding: there is no actual triangle, no
circumcenter, and no perpendicular distances — only three reals summing to `π`.

The parent's open question asks whether the genuinely *geometric* statement can
be formalized:

  > Can the metric signed-distance form with an explicit circumcenter over
  > `EuclideanSpace ℝ (Fin 2)` be formalized?

This file answers **yes**.  We build the triangle concretely in the Euclidean
plane `EuclideanSpace ℝ (Fin 2)`:

* the circumcenter is the **explicit point** `O = (0, 0)`;
* the three vertices `Pa, Pb, Pc` sit on the circle of radius `R` about `O`,
  placed by the inscribed-angle convention so that side `BC` subtends central
  angle `2A`, etc.;
* `O` is verified to be the circumcenter: `dist O Pa = dist O Pb = dist O Pc = R`
  (`circumradius`);
* for each side we exhibit the inward unit normal and take Mathlib's
  `signedDist` (the trilinear signed distance, `⟪normalize v, q -ᵥ p⟫`) from `O`
  to that side.

The geometric heart is that each signed distance is exactly `R cos` of the
opposite angle:

  `signedDist (na A) Pc O = R cos A`   (`dA_eq`),  and similarly `R cos B`, `R cos C`,

with the cosine carrying the correct sign automatically — negative precisely
when the circumcenter falls on the far side of an obtuse angle's opposite side.
We also certify each normal really is perpendicular to its side (`na_perp`,
`nb_perp`, `nc_perp`).

Summing and feeding the parent identity through gives **Carnot's theorem in
metric form**:

  `signedDist_a + signedDist_b + signedDist_c = R + r`,

where `r = 4 R sin(A/2) sin(B/2) sin(C/2)` is the inradius
(`carnot_signedDist_sum`).

**No axioms, no sorries.**
-/

open Real NormedSpace
open scoped RealInnerProductSpace

namespace CarnotTheoremOQ01OQ01OQ01

/-- The Euclidean plane. -/
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

/-! ## Coordinate helpers -/

/-- The norm of an explicit plane vector. -/
private lemma norm_two (a b : ℝ) :
    ‖(!₂[a, b] : Vec2)‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs]

/-- A vector `(a, b)` with `a² + b² = 1` is a unit vector. -/
private lemma norm_unit (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ‖(!₂[a, b] : Vec2)‖ = 1 := by
  rw [norm_two, h, Real.sqrt_one]

/-- A point on the circle of radius `r` has norm `r`. -/
private lemma norm_circle (r t : ℝ) (hr : 0 ≤ r) :
    ‖(!₂[r * Real.cos t, r * Real.sin t] : Vec2)‖ = r := by
  rw [norm_two,
    show (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq t]]
  exact Real.sqrt_sq hr

/-- The inner product of two explicit plane vectors. -/
private lemma inner_two (a b c d : ℝ) :
    ⟪(!₂[a, b] : Vec2), !₂[c, d]⟫ = a * c + b * d := by
  have h : ⟪(!₂[a, b] : Vec2), !₂[c, d]⟫ = c * a + d * b := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
  rw [h]; ring

/-! ## The configuration -/

/-- The circumcenter, placed at the origin. -/
def O : Vec2 := 0

/-- Vertex `A`, at position angle `2A + 2C` (so arc `CA = 2B`). -/
noncomputable def Pa (R A C : ℝ) : Vec2 := !₂[R * Real.cos (2 * A + 2 * C), R * Real.sin (2 * A + 2 * C)]

/-- Vertex `B`, at position angle `2A`. -/
noncomputable def Pb (R A : ℝ) : Vec2 := !₂[R * Real.cos (2 * A), R * Real.sin (2 * A)]

/-- Vertex `C`, at position angle `0`. -/
def Pc (R : ℝ) : Vec2 := !₂[R, 0]

/-- Inward unit normal to side `BC` (pointing toward `A`); midangle of `BC` is `A`. -/
noncomputable def na (A : ℝ) : Vec2 := !₂[-Real.cos A, -Real.sin A]

/-- Inward unit normal to side `CA` (pointing toward `B`); midangle of `CA` is `-B`. -/
noncomputable def nb (B : ℝ) : Vec2 := !₂[-Real.cos B, Real.sin B]

/-- Inward unit normal to side `AB` (pointing toward `C`); midangle of `AB` is `2A + C`. -/
noncomputable def nc (A C : ℝ) : Vec2 := !₂[-Real.cos (2 * A + C), -Real.sin (2 * A + C)]

/-! ## The circumcenter is genuine: equidistant from all three vertices -/

/-- `O` is the circumcenter: it is equidistant (`= R`) from the three vertices. -/
theorem circumradius (R A C : ℝ) (hR : 0 ≤ R) :
    dist O (Pa R A C) = R ∧ dist O (Pb R A) = R ∧ dist O (Pc R) = R := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [dist_eq_norm, O, zero_sub, norm_neg]
  · exact norm_circle R (2 * A + 2 * C) hR
  · exact norm_circle R (2 * A) hR
  · rw [Pc, norm_two]
    rw [show (R : ℝ) ^ 2 + (0 : ℝ) ^ 2 = R ^ 2 by ring, Real.sqrt_sq hR]

/-! ## The normals are unit vectors and perpendicular to their sides -/

private lemma norm_na (A : ℝ) : ‖na A‖ = 1 := by
  rw [na]; exact norm_unit _ _ (by nlinarith [Real.sin_sq_add_cos_sq A])

private lemma norm_nb (B : ℝ) : ‖nb B‖ = 1 := by
  rw [nb]; exact norm_unit _ _ (by nlinarith [Real.sin_sq_add_cos_sq B])

private lemma norm_nc (A C : ℝ) : ‖nc A C‖ = 1 := by
  rw [nc]; exact norm_unit _ _ (by nlinarith [Real.sin_sq_add_cos_sq (2 * A + C)])

/-- `na` is perpendicular to side `BC` (direction `Pc - Pb`). -/
theorem na_perp (R A : ℝ) : ⟪na A, Pc R - Pb R A⟫ = 0 := by
  rw [inner_sub_right, na, Pc, Pb, inner_two, inner_two]
  have h : Real.cos A * Real.cos (2 * A) + Real.sin A * Real.sin (2 * A) = Real.cos A := by
    rw [← Real.cos_sub, show A - 2 * A = -A by ring, Real.cos_neg]
  linear_combination R * h

/-- `nb` is perpendicular to side `CA` (direction `Pa - Pc`). -/
theorem nb_perp (R A B C : ℝ) (h : A + B + C = π) :
    ⟪nb B, Pa R A C - Pc R⟫ = 0 := by
  rw [inner_sub_right, nb, Pa, Pc, inner_two, inner_two]
  -- `B + (2A+2C) = 2π - B`, so `cos B cos(2A+2C) - sin B sin(2A+2C) = cos(2π - B) = cos B`.
  have key : Real.cos B * Real.cos (2 * A + 2 * C)
        - Real.sin B * Real.sin (2 * A + 2 * C) = Real.cos B := by
    rw [← Real.cos_add, show B + (2 * A + 2 * C) = 2 * π - B by linarith, Real.cos_sub]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  linear_combination (-R) * key

/-- `nc` is perpendicular to side `AB` (direction `Pa - Pb`). -/
theorem nc_perp (R A C : ℝ) :
    ⟪nc A C, Pa R A C - Pb R A⟫ = 0 := by
  rw [inner_sub_right, nc, Pa, Pb, inner_two, inner_two]
  -- midangle of `AB` is `2A + C`; both endpoints are equidistant in angle from it.
  have ha : Real.cos (2 * A + C) * Real.cos (2 * A + 2 * C)
        + Real.sin (2 * A + C) * Real.sin (2 * A + 2 * C) = Real.cos C := by
    rw [← Real.cos_sub, show (2 * A + C) - (2 * A + 2 * C) = -C by ring, Real.cos_neg]
  have hb : Real.cos (2 * A + C) * Real.cos (2 * A)
        + Real.sin (2 * A + C) * Real.sin (2 * A) = Real.cos C := by
    rw [← Real.cos_sub]; congr 1; ring
  linear_combination (-R) * ha + R * hb

/-! ## The signed distances are `R cos` of the opposite angle -/

/-- **Signed distance from the circumcenter to side `BC` equals `R cos A`.** -/
theorem dA_eq (R A : ℝ) : signedDist (na A) (Pc R) O = R * Real.cos A := by
  rw [signedDist_apply_apply, normalize_eq_self_of_norm_eq_one (norm_na A), vsub_eq_sub]
  simp only [O, zero_sub, inner_neg_right, na, Pc]
  rw [inner_two]; ring

/-- **Signed distance from the circumcenter to side `CA` equals `R cos B`.** -/
theorem dB_eq (R B : ℝ) : signedDist (nb B) (Pc R) O = R * Real.cos B := by
  rw [signedDist_apply_apply, normalize_eq_self_of_norm_eq_one (norm_nb B), vsub_eq_sub]
  simp only [O, zero_sub, inner_neg_right, nb, Pc]
  rw [inner_two]; ring

/-- **Signed distance from the circumcenter to side `AB` equals `R cos C`.** -/
theorem dC_eq (R A C : ℝ) : signedDist (nc A C) (Pb R A) O = R * Real.cos C := by
  rw [signedDist_apply_apply, normalize_eq_self_of_norm_eq_one (norm_nc A C), vsub_eq_sub]
  simp only [O, zero_sub, inner_neg_right, nc, Pb]
  rw [inner_two]
  have hcos : Real.cos (2 * A + C) * Real.cos (2 * A)
        + Real.sin (2 * A + C) * Real.sin (2 * A) = Real.cos C := by
    rw [← Real.cos_sub]; congr 1; ring
  linear_combination R * hcos

/-! ## Carnot's theorem, metric form -/

/-- **Carnot's theorem (metric signed-distance form).**

For a triangle with angles `A, B, C > 0` (`A + B + C = π`) and circumradius
`R > 0`, realized explicitly in `EuclideanSpace ℝ (Fin 2)` with circumcenter
`O = (0,0)`, the sum of the signed perpendicular distances from `O` to the three
sides equals `R + r`, where `r = 4 R sin(A/2) sin(B/2) sin(C/2)` is the inradius:

  `d_a + d_b + d_c = R + r`.

The signs are handled automatically by `signedDist`: a distance is negative
exactly when the circumcenter lies on the far side of the corresponding side
(the obtuse case).  The identity reduces, via `dA_eq`/`dB_eq`/`dC_eq`, to
`R (cos A + cos B + cos C) = R + r`, which is the parent angle identity scaled
by `R`.

Only `A + B + C = π` is needed for the identity itself; for a *genuine*
(non-degenerate) triangle one additionally takes `R > 0` and `A, B, C > 0`,
under which `circumradius` certifies that `O` really is the circumcenter. -/
theorem carnot_signedDist_sum (R A B C : ℝ) (h : A + B + C = π) :
    signedDist (na A) (Pc R) O + signedDist (nb B) (Pc R) O
        + signedDist (nc A C) (Pb R A) O
      = R + R * (4 * Real.sin (A / 2) * Real.sin (B / 2) * Real.sin (C / 2)) := by
  rw [dA_eq, dB_eq, dC_eq]
  have hsum := CarnotTheorem.carnot_cos_sum A B C h
  linear_combination R * hsum

end CarnotTheoremOQ01OQ01OQ01
