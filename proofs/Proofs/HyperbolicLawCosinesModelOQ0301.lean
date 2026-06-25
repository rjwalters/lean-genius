/-
Deriving the Hyperbolic Law of Cosines from the Hyperboloid Model

Open Question from: Hyperbolic Law of Cosines (law-of-cosines-oq-03), open
question oq-01:

  "Derive the hyperbolic law of cosines from the Poincaré disk model (or
   hyperboloid model): prove that the distance function satisfies
     cosh d(P,R) = cosh d(P,Q)·cosh d(Q,R) − sinh d(P,Q)·sinh d(Q,R)·cos∠PQR."

The parent entry *axiomatizes* the law of cosines as a structure field. This file
removes that assumption for the hyperboloid model: it **derives** the law from the
defining geometry of the model — the Minkowski bilinear form and the distance
`cosh d(u,v) = −⟨u,v⟩` — using nothing but `ring`/`nlinarith` and the standard
hyperbolic/trigonometric identities from Mathlib.

## The hyperboloid model

Hyperbolic 2-space is the upper sheet `H = {u ∈ ℝ^{2,1} : ⟨u,u⟩ = −1, u_t > 0}`
of the two-sheeted hyperboloid for the Minkowski form of signature `(−,+,+)`,
`⟨u,v⟩ = u_x v_x + u_y v_y − u_t v_t`.  The hyperbolic distance is recovered from
the ambient form by `cosh d(u,v) = −⟨u,v⟩`.

## The derivation, in one line

Place the angle vertex at the apex `O = (1,0,0)`.  A point at distance `r ≥ 0` in
direction `θ` is the geodesic-polar point `geo r θ = (cosh r, sinh r cos θ,
sinh r sin θ)`, which lies on `H` (because `cosh²−sinh² = 1` and `cos²+sin² = 1`)
and satisfies `d(O, geo r θ) = r`.  For the two sides `P = geo a 0`, `Q = geo b C`
with apex angle `C`, the Minkowski form computes the opposite side directly:

      −⟨P, Q⟩ = cosh a cosh b − sinh a sinh b cos C,

which, with `c := d(P,Q)`, is exactly `cosh c = cosh a cosh b − sinh a sinh b cos C`.
The value `−⟨P,Q⟩ ≥ 1` (reverse Cauchy–Schwarz, here `≥ cosh(a−b)`), so `c` is a
genuine distance.  That `C` is the true interior angle — not a free parameter — is
established separately: the initial velocities of the two geodesics at `O` are the
unit vectors `(0, cos θ, sin θ)`, whose induced (Euclidean) inner product is
`cos C`, so the angle is `arccos(cos C) = C`.

This vertex-at-apex placement is without loss of generality: the isometry group of
`H` acts transitively, with the apex stabilizer acting as Euclidean rotations of
the tangent plane, so every hyperbolic triangle is congruent to one in this
position (documented, not re-derived).

References:
- W. Thurston, *Three-Dimensional Geometry and Topology*, Princeton (1997), Ch. 2
- J. Ratcliffe, *Foundations of Hyperbolic Manifolds*, Springer, §3 (Lorentzian)
- B. Iversen, *Hyperbolic Geometry*, LMS Student Texts 25 (1992)

Tags: hyperbolic-geometry, law-of-cosines, hyperboloid-model, minkowski, lorentzian
-/

import Mathlib

open Real

namespace HyperbolicLawCosines

/-- A vector in `(2+1)`-dimensional Minkowski space `ℝ^{2,1}` with timelike
coordinate `t`. -/
structure Mvec where
  t : ℝ
  x : ℝ
  y : ℝ

/-- The Minkowski bilinear form of signature `(−,+,+)`:
`⟨u,v⟩ = uₓ vₓ + u_y v_y − u_t v_t`. -/
def mink (u v : Mvec) : ℝ := u.x * v.x + u.y * v.y - u.t * v.t

/-- The upper sheet of the hyperboloid — the hyperboloid model of the hyperbolic
plane: `⟨u,u⟩ = −1` together with `u_t > 0`. -/
def OnHyp (u : Mvec) : Prop := mink u u = -1 ∧ 0 < u.t

/-- Geodesic-polar coordinates about the apex `(1,0,0)`: the point at hyperbolic
distance `r` in the direction making angle `θ` with the `x`-axis. -/
noncomputable def geo (r θ : ℝ) : Mvec := ⟨cosh r, sinh r * cos θ, sinh r * sin θ⟩

/-- The apex (basepoint) of the model, `O = (1,0,0)`. -/
def apex : Mvec := ⟨1, 0, 0⟩

/-!
## Part I: The model is well-defined
-/

/-- Every geodesic-polar point lies on the hyperboloid: `⟨geo r θ, geo r θ⟩ = −1`
and its timelike coordinate is positive. -/
theorem geo_onHyp (r θ : ℝ) : OnHyp (geo r θ) := by
  refine ⟨?_, ?_⟩
  · simp only [mink, geo]
    linear_combination (sinh r ^ 2) * sin_sq_add_cos_sq θ - cosh_sq_sub_sinh_sq r
  · simp only [geo]; exact cosh_pos r

/-- The apex lies on the hyperboloid. -/
theorem apex_onHyp : OnHyp apex := by
  refine ⟨?_, ?_⟩ <;> simp [mink, apex]

/-!
## Part II: The law of cosines, derived from the Minkowski form
-/

/-- **The algebraic heart.** For the two sides `P = geo a 0` and `Q = geo b C`
issuing from the apex with angular separation `C`, the Minkowski form computes
the opposite side: `−⟨P,Q⟩ = cosh a cosh b − sinh a sinh b cos C`. -/
theorem mink_geo (a b C : ℝ) :
    - mink (geo a 0) (geo b C) = cosh a * cosh b - sinh a * sinh b * cos C := by
  simp only [mink, geo, cos_zero, sin_zero, mul_zero, mul_one, zero_mul]
  ring

/-- The opposite side value is `≥ 1`, hence a genuine value of `cosh` (reverse
Cauchy–Schwarz for the timelike form): `−⟨P,Q⟩ ≥ cosh(a−b) ≥ 1`. -/
theorem mink_geo_ge_one (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 ≤ - mink (geo a 0) (geo b C) := by
  rw [mink_geo]
  have hcsub : cosh (a - b) = cosh a * cosh b - sinh a * sinh b := cosh_sub a b
  have h1 : (1 : ℝ) ≤ cosh (a - b) := one_le_cosh _
  have hsa : 0 ≤ sinh a := sinh_nonneg_iff.mpr ha
  have hsb : 0 ≤ sinh b := sinh_nonneg_iff.mpr hb
  have hcos : 0 ≤ 1 - cos C := sub_nonneg.mpr (cos_le_one C)
  nlinarith [hcsub, h1, mul_nonneg (mul_nonneg hsa hsb) hcos]

/-- The hyperbolic distance between two model points: `arcosh(−⟨u,v⟩)`. -/
noncomputable def hdist (u v : Mvec) : ℝ := arcosh (- mink u v)

/-- **Hyperbolic law of cosines (standard form), derived.** With `c` the
hyperbolic length of the side opposite the apex angle `C`,
`cosh c = cosh a cosh b − sinh a sinh b cos C`. -/
theorem cosh_hdist_geo (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cosh (hdist (geo a 0) (geo b C))
      = cosh a * cosh b - sinh a * sinh b * cos C := by
  rw [hdist, cosh_arcosh (mink_geo_ge_one a b C ha hb), mink_geo]

/-- The geodesic side from the apex to `geo a θ` has hyperbolic length exactly `a`:
the parameters `a, b` really are the two adjacent side lengths. -/
theorem hdist_apex_geo (a θ : ℝ) (ha : 0 ≤ a) : hdist apex (geo a θ) = a := by
  rw [hdist]
  have h : - mink apex (geo a θ) = cosh a := by simp [mink, apex, geo]
  rw [h, arcosh_cosh ha]

/-- **Hyperbolic Pythagorean theorem.** A right angle at the apex (`C = π/2`)
collapses the law of cosines to `cosh c = cosh a cosh b`. -/
theorem hyperbolic_pythagoras (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cosh (hdist (geo a 0) (geo b (π / 2))) = cosh a * cosh b := by
  rw [cosh_hdist_geo a b _ ha hb, cos_pi_div_two]; ring

/-!
## Part III: `C` is the genuine interior angle at the apex

The interior angle is intrinsic data — the angle between the initial velocities of
the two geodesics measured in the induced Riemannian metric — not a free input.
We verify that this angle is exactly `C`.
-/

/-- The initial velocity (tangent at the apex, `r = 0`) of the geodesic
`r ↦ geo r θ`, namely `(0, cos θ, sin θ)`. -/
noncomputable def tangent (θ : ℝ) : Mvec := ⟨0, cos θ, sin θ⟩

/-- `tangent θ` really is the `t`-component velocity of `r ↦ geo r θ` at `r = 0`. -/
theorem geo_tangent_t (θ : ℝ) :
    HasDerivAt (fun r => (geo r θ).t) (tangent θ).t 0 := by
  simpa [geo, tangent] using (hasDerivAt_cosh 0)

/-- `tangent θ` really is the `x`-component velocity of `r ↦ geo r θ` at `r = 0`. -/
theorem geo_tangent_x (θ : ℝ) :
    HasDerivAt (fun r => (geo r θ).x) (tangent θ).x 0 := by
  simpa [geo, tangent] using ((hasDerivAt_sinh 0).mul_const (cos θ))

/-- `tangent θ` really is the `y`-component velocity of `r ↦ geo r θ` at `r = 0`. -/
theorem geo_tangent_y (θ : ℝ) :
    HasDerivAt (fun r => (geo r θ).y) (tangent θ).y 0 := by
  simpa [geo, tangent] using ((hasDerivAt_sinh 0).mul_const (sin θ))

/-- Each initial tangent is a unit vector for the induced metric (`mink` restricted
to the spacelike tangent plane at the apex is the Euclidean form). -/
theorem tangent_unit (θ : ℝ) : mink (tangent θ) (tangent θ) = 1 := by
  simp only [mink, tangent]
  linear_combination cos_sq_add_sin_sq θ

/-- The induced inner product of the two initial tangents is `cos C`. -/
theorem tangent_inner (C : ℝ) : mink (tangent 0) (tangent C) = cos C := by
  simp [mink, tangent]

/-- **The apex angle is `C`.** The angle between the two geodesics at the apex,
`arccos` of the (unit-normalized) inner product of their initial velocities, equals
`C` for `C ∈ [0, π]`. Hence `C` in the law of cosines is the genuine interior
angle, not an assumed parameter. -/
theorem apex_angle (C : ℝ) (h0 : 0 ≤ C) (hpi : C ≤ π) :
    arccos (mink (tangent 0) (tangent C)) = C := by
  rw [tangent_inner, arccos_cos h0 hpi]

end HyperbolicLawCosines
