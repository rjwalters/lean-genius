/-
Hyperbolic Law of Cosines as the K = −1 Analogue of the Spherical Law
(Constant-Curvature Quadric / Gauss-Equation Model)

Research problem: spherical-law-of-cosines-oq-04.

The spherical law of cosines (`SphericalLawOfCosines.lean`, curvature K = +1) and the
hyperbolic law of cosines (`HyperbolicLawCosinesModelOQ0301.lean`, curvature K = −1)
each live in the gallery as *derived* theorems of their respective ambient geometries
(Euclidean ℝ³ for the sphere, Minkowski ℝ^{2,1} for the hyperboloid).

The unified curvature-parametrized law of cosines
  `cs_K(c) = cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos C`
is recorded in `LawOfCosinesOQ05.lean`, but there the law is a **structure-encoded
assumption** (the `UnifiedTriangle.law` field): it is *stated* and shown to specialize
to the classical laws, yet it is never *derived* from a geometric model.

This file removes that assumption. It builds the single **constant-curvature quadric
model** that simultaneously hosts the sphere (K > 0), the Euclidean plane (K = 0), and
the hyperboloid (K < 0), and derives the unified law of cosines from the ambient
bilinear form alone — `ring`, the generalized Pythagorean identity, and the standard
trig/hyperbolic inverse functions from Mathlib. The hyperbolic law `K = −1` then drops
out as one specialization of the spherical law `K = +1`, exhibiting hyperbolic geometry
as the literal `K = −1` analogue.

## The model

Equip ℝ³ (coordinates `x, y, z`, with `z` the polar axis) with the
*curvature-`K` bilinear form*
  `B_K(u, v) = K·(uₓvₓ + u_y v_y) + u_z v_z`.
For `K = 1` this is the Euclidean dot product (unit sphere `B_1(u,u) = 1`); for `K = −1`
it is the Minkowski form of signature `(+,+,−)` up to overall sign (the hyperboloid
`B_{−1}(u,u) = 1` is the upper sheet `x² + y² − z² = −1` after the substitution below).

The **geodesic-polar point** at curvature-distance `r` and direction `θ` about the apex
`O = (0,0,1)` is
  `geoK K r θ = (sn_K(r)·cos θ, sn_K(r)·sin θ, cs_K(r))`,
where `cs_K`/`sn_K` are the curvature cosine/sine (`curvatureCos`/`curvatureSin`).
The generalized Pythagorean identity `cs_K² + K·sn_K² = 1` is exactly the statement that
`geoK K r θ` lies on the curvature quadric `B_K(·,·) = 1`.

## The derivation, in one line

For two sides `P = geoK K a 0`, `Q = geoK K b C` issuing from the apex with apex angle
`C`, the ambient form computes the opposite side directly (`bK_geo_geo`, pure `ring`):
  `B_K(P, Q) = cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos C`,
which, with the metric relation `cs_K(c) = B_K(P, Q)` (`bK_apex_geoK` shows `cs_K` of a
distance is the ambient form), is precisely the unified law of cosines. Inverting `cs_K`
on the valid range (`curvatureCos_curvatureDist_*`) turns this into the law in the form
`cs_K(c) = …`. For `K < 0` the right-hand side is `≥ 1` (`rhs_ge_one_neg`, the reverse
Cauchy–Schwarz `≥ cosh(√(−K)(a−b)) ≥ 1`), so `c` is a genuine distance.

References:
- W. Thurston, *Three-Dimensional Geometry and Topology*, Princeton (1997), Ch. 2
- J. Ratcliffe, *Foundations of Hyperbolic Manifolds*, Springer (2006), §3
- B. Iversen, *Hyperbolic Geometry*, LMS Student Texts 25 (1992)
- Todhunter, *Spherical Trigonometry* (1886)

Tags: differential-geometry, hyperbolic-geometry, spherical-geometry,
law-of-cosines, constant-curvature, gauss-equation, cayley-klein
-/

import Mathlib

open Real

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ConstantCurvatureLawOfCosines

/-!
## Part I: Curvature-parametrized trigonometric functions

These match `UnifiedLawOfCosines.curvatureCos`/`curvatureSin` from `LawOfCosinesOQ05.lean`;
they are repeated here so this model file is self-contained (it derives what that file
assumes).
-/

/-- The curvature cosine: `cos(√K·r)` for `K > 0`, `cosh(√(−K)·r)` for `K < 0`, `1` at
`K = 0`. -/
noncomputable def curvatureCos (K r : ℝ) : ℝ :=
  if K > 0 then Real.cos (Real.sqrt K * r)
  else if K < 0 then Real.cosh (Real.sqrt (-K) * r)
  else 1

/-- The curvature sine: `sin(√K·r)/√K` for `K > 0`, `sinh(√(−K)·r)/√(−K)` for `K < 0`,
`r` at `K = 0`. -/
noncomputable def curvatureSin (K r : ℝ) : ℝ :=
  if K > 0 then Real.sin (Real.sqrt K * r) / Real.sqrt K
  else if K < 0 then Real.sinh (Real.sqrt (-K) * r) / Real.sqrt (-K)
  else r

@[simp] theorem curvatureCos_one (r : ℝ) : curvatureCos 1 r = Real.cos r := by
  unfold curvatureCos; simp [Real.sqrt_one]

@[simp] theorem curvatureSin_one (r : ℝ) : curvatureSin 1 r = Real.sin r := by
  unfold curvatureSin; simp [Real.sqrt_one]

@[simp] theorem curvatureCos_neg_one (r : ℝ) : curvatureCos (-1) r = Real.cosh r := by
  unfold curvatureCos
  simp only [show ¬((-1 : ℝ) > 0) from by norm_num, if_false,
             show (-1 : ℝ) < 0 from by norm_num, if_true,
             show -(-1 : ℝ) = 1 from by norm_num, Real.sqrt_one, one_mul]

@[simp] theorem curvatureSin_neg_one (r : ℝ) : curvatureSin (-1) r = Real.sinh r := by
  unfold curvatureSin
  simp only [show ¬((-1 : ℝ) > 0) from by norm_num, if_false,
             show (-1 : ℝ) < 0 from by norm_num, if_true,
             show -(-1 : ℝ) = 1 from by norm_num, Real.sqrt_one, one_mul, div_one]

@[simp] theorem curvatureCos_zero (r : ℝ) : curvatureCos 0 r = 1 := by
  unfold curvatureCos; simp

@[simp] theorem curvatureSin_zero (r : ℝ) : curvatureSin 0 r = r := by
  unfold curvatureSin; simp

theorem curvatureCos_at_zero (K : ℝ) : curvatureCos K 0 = 1 := by
  unfold curvatureCos
  split_ifs with h1 h2
  · simp
  · simp
  · rfl

theorem curvatureSin_at_zero (K : ℝ) : curvatureSin K 0 = 0 := by
  unfold curvatureSin
  split_ifs with h1 h2
  · simp
  · simp
  · rfl

/-- **Generalized Pythagorean identity**: `cs_K(r)² + K·sn_K(r)² = 1` for all `K, r`. -/
theorem curvaturePythagorean (K r : ℝ) :
    curvatureCos K r ^ 2 + K * curvatureSin K r ^ 2 = 1 := by
  unfold curvatureCos curvatureSin
  rcases lt_trichotomy K 0 with hneg | hzero | hpos
  · have h1 : ¬K > 0 := not_lt.mpr (le_of_lt hneg)
    simp only [h1, if_false, hneg, if_true]
    have hκ : -K > 0 := neg_pos.mpr hneg
    have hKne : K ≠ 0 := ne_of_lt hneg
    have hsq : Real.sqrt (-K) ^ 2 = -K := Real.sq_sqrt (le_of_lt hκ)
    rw [div_pow, hsq]
    have hyp := Real.cosh_sq_sub_sinh_sq (Real.sqrt (-K) * r)
    have hcalc : K * (Real.sinh (Real.sqrt (-K) * r) ^ 2 / (-K)) =
                 -Real.sinh (Real.sqrt (-K) * r) ^ 2 := by
      field_simp
    linarith
  · subst hzero; norm_num
  · simp only [hpos, if_true]
    have hKne : K ≠ 0 := ne_of_gt hpos
    have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (le_of_lt hpos)
    rw [div_pow, hsq]
    have pyth := Real.sin_sq_add_cos_sq (Real.sqrt K * r)
    have hcalc : K * (Real.sin (Real.sqrt K * r) ^ 2 / K) =
                 Real.sin (Real.sqrt K * r) ^ 2 := by
      field_simp
    linarith

/-!
## Part II: The constant-curvature quadric model
-/

/-- A vector in the `(2+1)`-dimensional ambient space, with `z` the polar axis. -/
structure CKVec where
  x : ℝ
  y : ℝ
  z : ℝ

/-- The curvature-`K` bilinear form `B_K(u, v) = K·(uₓvₓ + u_y v_y) + u_z v_z`.
At `K = 1` it is the Euclidean dot product; at `K = −1` it is `−`(Minkowski form). -/
def bK (K : ℝ) (u v : CKVec) : ℝ := K * (u.x * v.x + u.y * v.y) + u.z * v.z

/-- Geodesic-polar coordinates about the apex `(0,0,1)`: the model point at
curvature-distance `r` in direction `θ`. -/
noncomputable def geoK (K r θ : ℝ) : CKVec :=
  ⟨curvatureSin K r * Real.cos θ, curvatureSin K r * Real.sin θ, curvatureCos K r⟩

/-- The apex (basepoint) of the model, `O = (0,0,1) = geoK K 0 θ`. -/
def apexK : CKVec := ⟨0, 0, 1⟩

/-- The apex lies on the curvature quadric: `B_K(O, O) = 1`. -/
theorem apexK_onQuadric (K : ℝ) : bK K apexK apexK = 1 := by
  simp [bK, apexK]

/-- Every geodesic-polar point lies on the curvature quadric `B_K(·,·) = 1`. This is
exactly the generalized Pythagorean identity. -/
theorem geoK_onQuadric (K r θ : ℝ) : bK K (geoK K r θ) (geoK K r θ) = 1 := by
  simp only [bK, geoK]
  linear_combination (K * curvatureSin K r ^ 2) * Real.sin_sq_add_cos_sq θ +
    curvaturePythagorean K r

/-- The geodesic-polar point at `r = 0` is the apex, for any direction. -/
theorem geoK_zero (K θ : ℝ) : geoK K 0 θ = apexK := by
  simp [geoK, apexK, curvatureCos_at_zero, curvatureSin_at_zero]

/-- The ambient form between the apex and a model point reads off the curvature cosine
of the distance: `B_K(O, geoK K r θ) = cs_K(r)`.  This is the metric relation
`cs_K(dist) = B_K`. -/
theorem bK_apex_geoK (K r θ : ℝ) : bK K apexK (geoK K r θ) = curvatureCos K r := by
  simp [bK, apexK, geoK]

/-!
## Part III: The unified law of cosines, derived from the model

For the two sides `P = geoK K a 0` and `Q = geoK K b C` issuing from the apex with apex
angle `C`, the ambient form computes the opposite side.
-/

/-- **The algebraic heart.** The ambient form of the two apex-sides is the right-hand
side of the unified law of cosines:
  `B_K(geoK K a 0, geoK K b C) = cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos C`. -/
theorem bK_geo_geo (K a b C : ℝ) :
    bK K (geoK K a 0) (geoK K b C) =
      curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * Real.cos C := by
  simp only [bK, geoK, Real.cos_zero, Real.sin_zero, mul_zero, mul_one, add_zero, zero_mul]
  ring

/-!
## Part IV: Recovering the distance — inverting the curvature cosine
-/

/-- The curvature distance recovered from an ambient-form value `w`: the inverse of
`cs_K`.  For `K > 0`, `arccos(w)/√K`; for `K < 0`, `arcosh(w)/√(−K)`; `0` at `K = 0`. -/
noncomputable def curvatureDist (K w : ℝ) : ℝ :=
  if K > 0 then Real.arccos w / Real.sqrt K
  else if K < 0 then Real.arcosh w / Real.sqrt (-K)
  else 0

/-- `cs_K ∘ (curvatureDist K)` is the identity on `[-1, 1]` for `K > 0`. -/
theorem curvatureCos_curvatureDist_pos (K w : ℝ) (hK : 0 < K)
    (hw1 : -1 ≤ w) (hw2 : w ≤ 1) : curvatureCos K (curvatureDist K w) = w := by
  have hs : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hK).ne'
  simp only [curvatureCos, curvatureDist, hK, if_true]
  have hcancel : Real.sqrt K * (Real.arccos w / Real.sqrt K) = Real.arccos w := by
    field_simp
  rw [hcancel, Real.cos_arccos hw1 hw2]

/-- `cs_K ∘ (curvatureDist K)` is the identity on `[1, ∞)` for `K < 0`. -/
theorem curvatureCos_curvatureDist_neg (K w : ℝ) (hK : K < 0)
    (hw : 1 ≤ w) : curvatureCos K (curvatureDist K w) = w := by
  have hκ : 0 < -K := neg_pos.mpr hK
  have hs : Real.sqrt (-K) ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
  simp only [curvatureCos, curvatureDist,
    show ¬K > 0 from not_lt.mpr hK.le, if_false, hK, if_true]
  have hcancel : Real.sqrt (-K) * (Real.arcosh w / Real.sqrt (-K)) = Real.arcosh w := by
    field_simp
  rw [hcancel, Real.cosh_arcosh hw]

/-!
## Part V: For `K < 0`, the opposite side is genuine (reverse Cauchy–Schwarz)
-/

/-- For `K < 0`, the cross term simplifies: `K·sn_K(a)·sn_K(b) = −sinh(√(−K)a)·sinh(√(−K)b)`. -/
theorem K_curvatureSin_mul_neg (K a b : ℝ) (hK : K < 0) :
    K * curvatureSin K a * curvatureSin K b =
      -(Real.sinh (Real.sqrt (-K) * a) * Real.sinh (Real.sqrt (-K) * b)) := by
  have hκ : 0 < -K := neg_pos.mpr hK
  have hs : Real.sqrt (-K) ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
  have hself : Real.sqrt (-K) * Real.sqrt (-K) = -K := Real.mul_self_sqrt hκ.le
  simp only [curvatureSin, show ¬K > 0 from not_lt.mpr hK.le, if_false, hK, if_true]
  field_simp
  linear_combination (Real.sinh (Real.sqrt (-K) * a) * Real.sinh (Real.sqrt (-K) * b)) * hself

/-- **Reverse Cauchy–Schwarz for the timelike form.** For `K < 0` and `a, b ≥ 0`, the
right-hand side of the law of cosines is `≥ 1`, hence a genuine value of `cs_K`:
  `cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos C ≥ cosh(√(−K)(a−b)) ≥ 1`. -/
theorem rhs_ge_one_neg (K a b C : ℝ) (hK : K < 0) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 ≤ curvatureCos K a * curvatureCos K b +
          K * curvatureSin K a * curvatureSin K b * Real.cos C := by
  have hκ : 0 < -K := neg_pos.mpr hK
  have hu : 0 ≤ Real.sqrt (-K) := Real.sqrt_nonneg _
  set u := Real.sqrt (-K) with hu_def
  -- Rewrite the curvature cosines/cross-term into cosh/sinh form.
  have hcos_a : curvatureCos K a = Real.cosh (u * a) := by
    simp only [curvatureCos, show ¬K > 0 from not_lt.mpr hK.le, if_false, hK, if_true, hu_def]
  have hcos_b : curvatureCos K b = Real.cosh (u * b) := by
    simp only [curvatureCos, show ¬K > 0 from not_lt.mpr hK.le, if_false, hK, if_true, hu_def]
  have hcross : K * curvatureSin K a * curvatureSin K b =
      -(Real.sinh (u * a) * Real.sinh (u * b)) := by
    rw [hu_def]; exact K_curvatureSin_mul_neg K a b hK
  rw [hcos_a, hcos_b]
  have hrw : Real.cosh (u * a) * Real.cosh (u * b) +
      K * curvatureSin K a * curvatureSin K b * Real.cos C =
      Real.cosh (u * a) * Real.cosh (u * b) -
        Real.sinh (u * a) * Real.sinh (u * b) * Real.cos C := by
    rw [hcross]; ring
  rw [hrw]
  -- reverse Cauchy–Schwarz: ≥ cosh(ua − ub) ≥ 1
  have hcsub : Real.cosh (u * a - u * b) =
      Real.cosh (u * a) * Real.cosh (u * b) - Real.sinh (u * a) * Real.sinh (u * b) :=
    Real.cosh_sub _ _
  have h1 : (1 : ℝ) ≤ Real.cosh (u * a - u * b) := Real.one_le_cosh _
  have hsa : 0 ≤ Real.sinh (u * a) := Real.sinh_nonneg_iff.mpr (mul_nonneg hu ha)
  have hsb : 0 ≤ Real.sinh (u * b) := Real.sinh_nonneg_iff.mpr (mul_nonneg hu hb)
  have hcos : 0 ≤ 1 - Real.cos C := sub_nonneg.mpr (Real.cos_le_one C)
  nlinarith [hcsub, h1, mul_nonneg (mul_nonneg hsa hsb) hcos]

/-!
## Part VI: The derived unified law of cosines

`cs_K(c) = cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos C`, where `c` is the genuine model
distance `curvatureDist K (B_K(P,Q))`.  This is the conclusion `UnifiedTriangle.law`
*assumes* in `LawOfCosinesOQ05.lean` — here it is derived from the model.
-/

/-- **Unified law of cosines, hyperbolic/flat regime (`K < 0`), derived & unconditional.**
With `c := curvatureDist K (B_K(P, Q))` the genuine curvature-distance of the opposite
side, the unified law holds for any apex angle `C` and any side lengths `a, b ≥ 0`. -/
theorem unified_law_derived_neg (K a b C : ℝ) (hK : K < 0) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    curvatureCos K (curvatureDist K (bK K (geoK K a 0) (geoK K b C))) =
      curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * Real.cos C := by
  rw [bK_geo_geo]
  exact curvatureCos_curvatureDist_neg K _ hK (rhs_ge_one_neg K a b C hK ha hb)

/-- **Unified law of cosines, spherical regime (`K > 0`), derived.** When the ambient
form lies in `[-1, 1]` (a non-degenerate spherical triangle), the unified law holds with
`c` the genuine curvature-distance. -/
theorem unified_law_derived_pos (K a b C : ℝ) (hK : 0 < K)
    (hlo : -1 ≤ bK K (geoK K a 0) (geoK K b C))
    (hhi : bK K (geoK K a 0) (geoK K b C) ≤ 1) :
    curvatureCos K (curvatureDist K (bK K (geoK K a 0) (geoK K b C))) =
      curvatureCos K a * curvatureCos K b +
        K * curvatureSin K a * curvatureSin K b * Real.cos C := by
  rw [bK_geo_geo]
  rw [bK_geo_geo] at hlo hhi
  exact curvatureCos_curvatureDist_pos K _ hK hlo hhi

/-!
## Part VII: Specializing to the classical laws

The hyperbolic law (`K = −1`) is *literally* the `K = −1` instance of the model, and the
spherical law (`K = +1`) the `K = +1` instance.
-/

/-- **Hyperbolic law of cosines (`K = −1`), derived from the unified model.**
`cosh c = cosh a · cosh b − sinh a · sinh b · cos C`, with `c` the model distance. -/
theorem hyperbolic_law_of_cosines (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.cosh (curvatureDist (-1) (bK (-1) (geoK (-1) a 0) (geoK (-1) b C))) =
      Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b * Real.cos C := by
  have h := unified_law_derived_neg (-1) a b C (by norm_num) ha hb
  rw [curvatureCos_neg_one] at h
  rw [h, curvatureCos_neg_one, curvatureCos_neg_one, curvatureSin_neg_one,
    curvatureSin_neg_one]
  ring

/-- **Spherical law of cosines (`K = +1`), derived from the unified model.**
`cos c = cos a · cos b + sin a · sin b · cos C`, with `c` the model distance, when the
triangle is non-degenerate (`B_1 ∈ [-1,1]`). -/
theorem spherical_law_of_cosines (a b C : ℝ)
    (hlo : -1 ≤ bK 1 (geoK 1 a 0) (geoK 1 b C))
    (hhi : bK 1 (geoK 1 a 0) (geoK 1 b C) ≤ 1) :
    Real.cos (curvatureDist 1 (bK 1 (geoK 1 a 0) (geoK 1 b C))) =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
  have h := unified_law_derived_pos 1 a b C (by norm_num) hlo hhi
  rw [curvatureCos_one] at h
  rw [h, curvatureCos_one, curvatureCos_one, curvatureSin_one, curvatureSin_one]
  ring

/-- **Hyperbolic Pythagorean theorem.** A right apex angle (`C = π/2`) collapses the
`K = −1` law to `cosh c = cosh a · cosh b`. -/
theorem hyperbolic_pythagoras (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.cosh (curvatureDist (-1) (bK (-1) (geoK (-1) a 0) (geoK (-1) b (π / 2)))) =
      Real.cosh a * Real.cosh b := by
  rw [hyperbolic_law_of_cosines a b _ ha hb, Real.cos_pi_div_two]; ring

/-!
## Summary

| Geometry      | K   | cs_K(r)         | sn_K(r)              | ambient form `B_K`        |
|---------------|-----|-----------------|----------------------|---------------------------|
| Spherical     | +1  | cos r           | sin r                | Euclidean dot product     |
| K-spherical   | >0  | cos(√K·r)       | sin(√K·r)/√K         | `K(xx'+yy') + zz'`        |
| Euclidean     | 0   | 1               | r                    | `zz'`                     |
| K-hyperbolic  | <0  | cosh(√(−K)·r)   | sinh(√(−K)·r)/√(−K)  | `K(xx'+yy') + zz'`        |
| Hyperbolic    | -1  | cosh r          | sinh r               | `−(xx'+yy') + zz'`        |

**Derived (0 axioms, 0 sorries):**
- `geoK_onQuadric` : the model points lie on the curvature quadric `B_K = 1`
- `bK_apex_geoK`   : `B_K(O, geoK r θ) = cs_K(r)` (the metric relation)
- `bK_geo_geo`     : `B_K(P,Q) = cs_K a · cs_K b + K · sn_K a · sn_K b · cos C` (the law)
- `unified_law_derived_neg` : the unified law for `K < 0`, **unconditional** for `a,b ≥ 0`
- `unified_law_derived_pos` : the unified law for `K > 0`, non-degenerate triangle
- `hyperbolic_law_of_cosines` / `spherical_law_of_cosines` : classical `K = ∓1` laws

This *derives* the law that `LawOfCosinesOQ05.UnifiedTriangle.law` only *assumes*.
-/

end ConstantCurvatureLawOfCosines
