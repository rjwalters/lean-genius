/-
# Spherical Law of Cosines — OQ-03: the Dual (angles) Law of Cosines

Research file for OQ-03 of the parent gallery entry `spherical-law-of-cosines`.

## The OPEN question

The parent `SphericalLawOfCosines.lean` proves the **side** law of cosines

  cos c = cos a · cos b + sin a · sin b · cos C

for a spherical triangle with arc-length sides `a, b, c` and interior
angle `C` opposite side `c`.

OQ-03 asks to formalise the **dual** (angles) law of cosines:

  cos C = − cos A · cos B + sin A · sin B · cos c

This is the polar dual of the side law: it expresses the cosine of an
*angle* via the other two *angles* and the *included side*. The minus
sign in front of `cos A · cos B` is the hallmark of spherical duality
(the polar triangle has sides `π − A` and angles `π − a`).

## Strategy: a radical-free, division-free formalisation

We avoid all square roots and divisions (which would force non-degeneracy
side-conditions) by clearing denominators. Work with vectors in ℝ³ as a
3-field structure `V`, with the dot product `dot` and cross product
`cross`. For a spherical triangle given by three unit vectors `u, v, w`,
the side cosines are

  ca = ⟨v, w⟩ = cos a,   cb = ⟨w, u⟩ = cos b,   cc = ⟨u, v⟩ = cos c.

The standard spherical-trig identities express the interior angle cosines
and sines in *normal form*

  cos A = (ca − cb·cc)/(sin b · sin c),   sin A = |[u v w]|/(sin b · sin c)

where `[u v w] = ⟨u, v × w⟩` is the scalar triple product and
`sin a = √(1 − ca²)`. (These are exactly the parent's side law solved for
the angle, together with `‖v × w‖ = sin a`.) Substituting these into the
trig dual law and multiplying through by `sin a · sin b · sin² c` turns it
into the **polynomial identity** `dual_poly`, proved by `ring`.

The geometric content then becomes `dual_spherical_law_cleared`:

  (cc − ca·cb)·(1 − cc²) = −(ca − cb·cc)(cb − ca·cc) + [u v w]²·cc

for any three unit vectors. Here `1 − cc² = sin² c` and `[u v w]² = sin² A · sin² b · sin² c`
is the Gram determinant; dividing by `sin a · sin b · sin² c` recovers the
trig form `cos C = − cos A · cos B + sin A · sin B · cos c`.

## Contents

* `binet_cauchy`         — `⟨a×b, c×d⟩ = ⟨a,c⟩⟨b,d⟩ − ⟨a,d⟩⟨b,c⟩`           (ring)
* `lagrange_identity`    — `‖a×b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²`                       (ring)
* `triple_sq`            — `[u v w]² = Gram determinant`                       (ring)
* `dot_cross_self_*`     — `⟨a×b, a⟩ = 0`, `⟨a×b, b⟩ = 0`                       (ring)
* `cross_norm_sq_nonneg` / `one_sub_sq_nonneg` — side sines are well defined
* `dual_poly`            — algebraic heart of the dual law                     (ring)
* `dual_law_cleared`     — dual law for abstract normal-form data
* `dual_spherical_law_cleared` — dual law for a unit-vector spherical triangle
* `dual_law_trig`        — literal trig dual law from cleared normal-form hypotheses
* `cosA_num`/`cosB_num`/`cosC_num` — angle-cosine numerators as Binet–Cauchy
  inner products of edge normals (geometric grounding of the normal forms)
* `sina_sq`/`sinb_sq`/`sinc_sq` — side-sine squares as Lagrange self-inner-products
* `dual_law_cross_product_form` — the dual law in pure cross-product form
* `polar_inner_uv`/`polar_inner_vw`/`polar_inner_wu` — polar-vertex inner products,
  the `π − ·` side/angle swap of polar duality (`⟨v×w, w×u⟩ = cos a·cos b − cos c`)
* `polar_self_uu`/`polar_self_vv`/`polar_self_ww` — polar side-sine squares
* `dual_law_polar_form` — the dual law as a side-law relation among the polar vertices
  (the structural realisation of the polar-triangle duality)

Axioms: 0.  Sorries: 0.

NOTE (build provenance): authored during a Docker + Aristotle backend
outage, so it has not yet been machine-checked locally. All proofs are
`ring`/`rw`+`ring`/`nlinarith` only (no `field_simp`, no division), and
the underlying identities were verified numerically over 2·10⁵ random
spherical triangles to ≤ 2·10⁻¹⁴ (see
`research/scripts/verify-spherical-dual.py`).
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace SphericalLawOfCosinesOQ03

open Real

/-! ## Part I: 3-vectors, dot and cross products -/

/-- A vector in ℝ³. -/
structure V where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Euclidean dot product on ℝ³. -/
def dot (u v : V) : ℝ := u.x * v.x + u.y * v.y + u.z * v.z

/-- Cross product on ℝ³. -/
def cross (u v : V) : V :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩

/-- Scalar triple product `[u v w] = ⟨u, v × w⟩`. -/
def triple (u v w : V) : ℝ := dot u (cross v w)

theorem dot_comm (u v : V) : dot u v = dot v u := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v
  simp only [dot]; ring

/-! ## Part II: Binet–Cauchy and Gram identities (pure `ring`) -/

/-- **Binet–Cauchy identity**:
    `⟨a × b, c × d⟩ = ⟨a, c⟩⟨b, d⟩ − ⟨a, d⟩⟨b, c⟩`. -/
theorem binet_cauchy (a b c d : V) :
    dot (cross a b) (cross c d) = dot a c * dot b d - dot a d * dot b c := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c; obtain ⟨d1, d2, d3⟩ := d
  simp only [dot, cross]; ring

/-- **Lagrange identity**: `‖a × b‖² = ‖a‖²‖b‖² − ⟨a, b⟩²`. -/
theorem lagrange_identity (a b : V) :
    dot (cross a b) (cross a b) = dot a a * dot b b - dot a b * dot a b := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [dot, cross]; ring

/-- The cross product is orthogonal to its first factor. -/
theorem dot_cross_left (a b : V) : dot (cross a b) a = 0 := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [dot, cross]; ring

/-- The cross product is orthogonal to its second factor. -/
theorem dot_cross_right (a b : V) : dot (cross a b) b = 0 := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [dot, cross]; ring

/-- The squared scalar triple product equals the Gram determinant of `u, v, w`. -/
theorem triple_sq (u v w : V) :
    (triple u v w) ^ 2 =
      dot u u * dot v v * dot w w
      + 2 * dot u v * dot v w * dot w u
      - dot u u * dot v w ^ 2
      - dot v v * dot w u ^ 2
      - dot w w * dot u v ^ 2 := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v; obtain ⟨w1, w2, w3⟩ := w
  simp only [triple, dot, cross]; ring

/-- `‖a × b‖² ≥ 0`, expressed via `dot`. -/
theorem cross_norm_sq_nonneg (a b : V) : 0 ≤ dot (cross a b) (cross a b) := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [dot, cross]
  nlinarith [sq_nonneg (a2 * b3 - a3 * b2), sq_nonneg (a3 * b1 - a1 * b3),
    sq_nonneg (a1 * b2 - a2 * b1)]

/-- For unit vectors, the side cosine satisfies `cos² ≤ 1`, so `sin² = 1 − cos² ≥ 0`
    and the side sine `√(1 − cos²)` is well defined (spherical Cauchy–Schwarz). -/
theorem one_sub_sq_nonneg (u v : V) (hu : dot u u = 1) (hv : dot v v = 1) :
    0 ≤ 1 - dot u v ^ 2 := by
  have hL := lagrange_identity u v
  have hnn := cross_norm_sq_nonneg u v
  rw [hL, hu, hv] at hnn
  nlinarith [hnn]

/-! ## Part III: The algebraic heart of the dual law -/

/-- **Polynomial identity underlying the dual law of cosines.**

For real side cosines `ca, cb, cc`:

  `(cc − ca·cb)(1 − cc²) = −(ca − cb·cc)(cb − ca·cc) + (1 − ca² − cb² − cc² + 2·ca·cb·cc)·cc`.

The left factor `1 − cc²` is `sin² c`, the last factor is the squared
triple product `[u v w]²` (the Gram determinant), and the bracketed
differences are the numerators of the normal-form angle cosines.
Dividing through produces the dual law. -/
theorem dual_poly (ca cb cc : ℝ) :
    (cc - ca * cb) * (1 - cc ^ 2) =
      -(ca - cb * cc) * (cb - ca * cc)
        + (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc) * cc := by
  ring

/-- **Dual spherical law of cosines (cleared, abstract form).**

Given side cosines `ca, cb, cc`, the squared side sine `sc2 = 1 − cc²`,
and a squared triple product `tp2 = 1 − ca² − cb² − cc² + 2·ca·cb·cc`,

  `(cc − ca·cb)·sc2 = −(ca − cb·cc)(cb − ca·cc) + tp2·cc`.

Dividing both sides by `sin a · sin b · sin² c` and using
`cos A = (ca − cb·cc)/(sin b · sin c)`, `sin A = √tp2/(sin b · sin c)`,
etc. gives the trig dual law `cos C = − cos A·cos B + sin A·sin B·cos c`. -/
theorem dual_law_cleared
    (ca cb cc sc2 tp2 : ℝ)
    (hsc : sc2 = 1 - cc ^ 2)
    (htp : tp2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc) :
    (cc - ca * cb) * sc2 = -(ca - cb * cc) * (cb - ca * cc) + tp2 * cc := by
  rw [hsc, htp]; ring

/-! ## Part IV: The geometric dual law for a unit-vector spherical triangle -/

/-- **Dual spherical law of cosines** for a spherical triangle given by
unit vectors `u, v, w`, in cleared (radical-free, division-free) form.

With side cosines `ca = ⟨v,w⟩` (= cos a), `cb = ⟨w,u⟩` (= cos b),
`cc = ⟨u,v⟩` (= cos c), and scalar triple product `[u v w]`:

  `(cc − ca·cb)·(1 − cc²) = −(ca − cb·cc)(cb − ca·cc) + [u v w]²·cc`.

Here `1 − cc² = sin² c` and `[u v w]² = sin²A · sin²b · sin²c` is the Gram
determinant, so dividing by `sin a · sin b · sin² c` yields exactly

  `cos C = − cos A · cos B + sin A · sin B · cos c`. -/
theorem dual_spherical_law_cleared
    (u v w : V) (hu : dot u u = 1) (hv : dot v v = 1) (hw : dot w w = 1) :
    (dot u v - dot v w * dot w u) * (1 - dot u v ^ 2)
      = -(dot v w - dot w u * dot u v) * (dot w u - dot v w * dot u v)
        + (triple u v w) ^ 2 * dot u v := by
  have htp := triple_sq u v w
  rw [hu, hv, hw] at htp
  rw [htp]; ring

/-! ## Part V: The literal trigonometric dual law `cos C = − cos A·cos B + sin A·sin B·cos c` -/

/-- **Literal trigonometric dual law of cosines.** From the angle cos/sin defining
relations taken in *cleared product form* (the side law solved for the angle with
denominators cleared) plus the side-Pythagorean identity `sc² = 1 − cc²`, the dual
spherical law of cosines holds as the literal equality

  `cos C = − cos A · cos B + sin A · sin B · cos c`.

Division-free route (no `field_simp`): the angle relations are posited cleared, the
common denominator `sa·sb·sc²` is removed once via `mul_right_cancel₀`, and the goal
closes by a single `linear_combination` against `dual_law_cleared` (the polynomial
heart) — both coefficients sympy-verified in `verify_dual_trig.py`. -/
theorem dual_law_trig
    (ca cb cc sa sb sc cA cB cC sA sB : ℝ)
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) (hsc : sc ≠ 0)
    (hsc2 : sc ^ 2 = 1 - cc ^ 2)
    (hcA : cA * (sb * sc) = ca - cb * cc)
    (hcB : cB * (sa * sc) = cb - ca * cc)
    (hcC : cC * (sa * sb) = cc - ca * cb)
    (hsAsB : sA * sB * (sa * sb * sc ^ 2)
        = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc) :
    cC = -cA * cB + sA * sB * cc := by
  have hD : sa * sb * sc ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsa hsb) (pow_ne_zero 2 hsc)
  have hAB : cA * cB * (sa * sb * sc ^ 2) = (ca - cb * cc) * (cb - ca * cc) := by
    have h : cA * (sb * sc) * (cB * (sa * sc)) = (ca - cb * cc) * (cb - ca * cc) := by
      rw [hcA, hcB]
    linear_combination h
  have key : (cc - ca * cb) * sc ^ 2
      = -(ca - cb * cc) * (cb - ca * cc)
        + (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc) * cc :=
    dual_law_cleared ca cb cc (sc ^ 2)
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc) hsc2 rfl
  apply mul_right_cancel₀ hD
  linear_combination (sc ^ 2) * hcC + hAB - cc * hsAsB + key

/-! ## Part VI: Fully geometric cross-product form

The cleared dual law `dual_spherical_law_cleared` is stated with the angle-cosine
*numerators* `ca − cb·cc`, etc. and the side-sine *squares* `1 − cc²` written out
as polynomials in the side cosines. The lemmas below show that each of those
quantities is itself a transparent cross-product inner product:

* every angle-cosine numerator is a Binet–Cauchy inner product of two edge normals
  (`⟨u×v, u×w⟩ = cos a − cos b·cos c`, the unnormalised `cos A`);
* every side-sine square is a Lagrange self-inner-product
  (`⟨u×v, u×v⟩ = 1 − cos²c = sin²c`).

Substituting these identifications recovers the dual law in **pure cross-product
form** (`dual_law_cross_product_form`), with no side cosines appearing as bare
inner products — the entire identity lives in the exterior algebra of the three
vertex vectors. This grounds the posited normal forms of `dual_law_trig` in actual
geometry; all proofs remain `ring`/`rw`-only (no division, no radicals). -/

/-- Angle `A` (at vertex `u`) numerator as a Binet–Cauchy inner product of the two
edge normals at `u`:  `⟨u×v, u×w⟩ = cos a − cos b·cos c`. -/
theorem cosA_num (u v w : V) (hu : dot u u = 1) :
    dot (cross u v) (cross u w) = dot v w - dot w u * dot u v := by
  have h := binet_cauchy u v u w
  rw [h, hu, dot_comm u w, dot_comm v u]; ring

/-- Angle `B` (at vertex `v`) numerator as a Binet–Cauchy inner product of the two
edge normals at `v`:  `⟨v×w, v×u⟩ = cos b − cos a·cos c`. -/
theorem cosB_num (u v w : V) (hv : dot v v = 1) :
    dot (cross v w) (cross v u) = dot w u - dot v w * dot u v := by
  have h := binet_cauchy v w v u
  rw [h, hv, dot_comm v u, dot_comm w v]; ring

/-- Angle `C` (at vertex `w`) numerator as a Binet–Cauchy inner product of the two
edge normals at `w`:  `⟨w×u, w×v⟩ = cos c − cos a·cos b`. -/
theorem cosC_num (u v w : V) (hw : dot w w = 1) :
    dot (cross w u) (cross w v) = dot u v - dot v w * dot w u := by
  have h := binet_cauchy w u w v
  rw [h, hw, dot_comm w v, dot_comm u w]; ring

/-- Side `c` sine-square as a Lagrange self-inner-product:
`⟨u×v, u×v⟩ = 1 − cos²c = sin²c`. -/
theorem sinc_sq (u v : V) (hu : dot u u = 1) (hv : dot v v = 1) :
    dot (cross u v) (cross u v) = 1 - dot u v ^ 2 := by
  rw [lagrange_identity u v, hu, hv]; ring

/-- Side `b` sine-square as a Lagrange self-inner-product:
`⟨w×u, w×u⟩ = 1 − cos²b = sin²b`. -/
theorem sinb_sq (u w : V) (hw : dot w w = 1) (hu : dot u u = 1) :
    dot (cross w u) (cross w u) = 1 - dot w u ^ 2 := by
  rw [lagrange_identity w u, hw, hu]; ring

/-- Side `a` sine-square as a Lagrange self-inner-product:
`⟨v×w, v×w⟩ = 1 − cos²a = sin²a`. -/
theorem sina_sq (v w : V) (hv : dot v v = 1) (hw : dot w w = 1) :
    dot (cross v w) (cross v w) = 1 - dot v w ^ 2 := by
  rw [lagrange_identity v w, hv, hw]; ring

/-- **Dual spherical law of cosines, pure cross-product form.**

For a spherical triangle given by unit vectors `u, v, w`, the cleared dual law
holds with *every* angle-cosine numerator and side-sine square replaced by its
cross-product realisation:

  `⟨w×u, w×v⟩ · ⟨u×v, u×v⟩ = −⟨u×v, u×w⟩ · ⟨v×w, v×u⟩ + [u v w]² · ⟨u, v⟩`.

Reading off the geometric meaning (`⟨w×u,w×v⟩ = sin a sin b cos C`,
`⟨u×v,u×v⟩ = sin²c`, `[u v w]² = sin²A sin²b sin²c`, etc.) and dividing by the
positive product of side sines recovers `cos C = −cos A cos B + sin A sin B cos c`.
Proved by rewriting the four cross-product quantities to their side-cosine normal
forms (`cosA_num`/`cosB_num`/`cosC_num`/`sinc_sq`) and invoking
`dual_spherical_law_cleared`. -/
theorem dual_law_cross_product_form
    (u v w : V) (hu : dot u u = 1) (hv : dot v v = 1) (hw : dot w w = 1) :
    dot (cross w u) (cross w v) * dot (cross u v) (cross u v)
      = -(dot (cross u v) (cross u w)) * dot (cross v w) (cross v u)
        + (triple u v w) ^ 2 * dot u v := by
  rw [cosC_num u v w hw, sinc_sq u v hu hv, cosA_num u v w hu, cosB_num u v w hv]
  exact dual_spherical_law_cleared u v w hu hv hw

/-! ## Part VII: Polar-triangle duality — the dual law is a side relation among polar vertices

The OQ's significance is the *polar-triangle duality*: the dual (angles) law is the
primal (sides) law applied to the **polar triangle**. For a spherical triangle with unit
vertices `u, v, w`, the (unnormalised) polar-triangle vertices are the edge normals

  `U = v × w`,   `V = w × u`,   `W = u × v`,

i.e. each polar vertex is perpendicular to the great-circle plane of the opposite side.
Classically the polar triangle has sides `π − A` and angles `π − a`, so the cosine of a
polar *side* is `−` the cosine of an original *angle*. The inner products among the polar
vertices realise exactly this swap, in cleared (radical-free) form:

* `polar_inner_uv` : `⟨U, V⟩ = cos a·cos b − cos c` (`= −(cos c − cos a·cos b)`, the negated
  `cos C` numerator — the polar side opposite `W` carries `cos c' = −cos C`);
* `polar_self_*`   : `⟨U, U⟩ = 1 − cos²a = sin²a` (the polar side sine equals the original
  vertex-angle sine, `sin a' = sin A`).

Substituting these into `dual_spherical_law_cleared` re-expresses the dual law entirely in
terms of polar-vertex inner products (`dual_law_polar_form`): the dual law of `T` is a
side-law-type relation among the vertices of the polar triangle `T'`. This is the structural
"why" of the duality, derived (not merely asserted) within the file's own cross-product
algebra — all proofs `ring`/`rw`-only, no division, no radicals. -/

/-- Polar-vertex inner product `⟨v×w, w×u⟩ = cos a·cos b − cos c`.

This is `−(cos c − cos a·cos b)`, the negated numerator of `cos C`: the polar side opposite
vertex `W = u×v` has cosine `cos c' = −cos C`, the hallmark `π − C` swap of polar duality. -/
theorem polar_inner_uv (u v w : V) (hw : dot w w = 1) :
    dot (cross v w) (cross w u) = dot v w * dot w u - dot u v := by
  have h := binet_cauchy v w w u
  rw [h, hw, dot_comm v u]; ring

/-- Polar-vertex inner product `⟨w×u, u×v⟩ = cos b·cos c − cos a`
(`= −(cos a − cos b·cos c)`, the negated numerator of `cos A`). -/
theorem polar_inner_vw (u v w : V) (hu : dot u u = 1) :
    dot (cross w u) (cross u v) = dot w u * dot u v - dot v w := by
  have h := binet_cauchy w u u v
  rw [h, hu, dot_comm w v]; ring

/-- Polar-vertex inner product `⟨u×v, v×w⟩ = cos c·cos a − cos b`
(`= −(cos b − cos a·cos c)`, the negated numerator of `cos B`). -/
theorem polar_inner_wu (u v w : V) (hv : dot v v = 1) :
    dot (cross u v) (cross v w) = dot u v * dot v w - dot w u := by
  have h := binet_cauchy u v v w
  rw [h, hv, dot_comm u w]; ring

/-- Polar side opposite `U`: `⟨v×w, v×w⟩ = 1 − cos²a = sin²a`
(`= sin²a'` only up to the duality `sin a' = sin A`; here it is literally `sin²a`). -/
theorem polar_self_uu (v w : V) (hv : dot v v = 1) (hw : dot w w = 1) :
    dot (cross v w) (cross v w) = 1 - dot v w ^ 2 := sina_sq v w hv hw

/-- Polar side opposite `V`: `⟨w×u, w×u⟩ = 1 − cos²b = sin²b`. -/
theorem polar_self_vv (u w : V) (hw : dot w w = 1) (hu : dot u u = 1) :
    dot (cross w u) (cross w u) = 1 - dot w u ^ 2 := sinb_sq u w hw hu

/-- Polar side opposite `W`: `⟨u×v, u×v⟩ = 1 − cos²c = sin²c`. -/
theorem polar_self_ww (u v : V) (hu : dot u u = 1) (hv : dot v v = 1) :
    dot (cross u v) (cross u v) = 1 - dot u v ^ 2 := sinc_sq u v hu hv

/-- **Dual spherical law of cosines, polar form.**

The dual law re-expressed entirely in inner products of the polar-triangle vertices
`U = v×w`, `V = w×u`, `W = u×v` (with the included side cosine `⟨u, v⟩ = cos c` and the
Gram determinant `[u v w]²`):

  `−⟨v×w, w×u⟩ · ⟨u×v, u×v⟩ = −⟨w×u, u×v⟩ · ⟨u×v, v×w⟩ + [u v w]² · ⟨u, v⟩`.

Each polar inner product is the (negated) cosine numerator / side-sine square of the
original triangle (`polar_inner_*`, `polar_self_ww`), so this is `dual_spherical_law_cleared`
read in the polar triangle's own coordinates: the dual law of `T` *is* a side-law-shaped
relation among the vertices of the polar triangle `T'`. Proof: rewrite the polar inner
products to side-cosine normal forms, then it is `dual_spherical_law_cleared` verbatim. -/
theorem dual_law_polar_form
    (u v w : V) (hu : dot u u = 1) (hv : dot v v = 1) (hw : dot w w = 1) :
    -dot (cross v w) (cross w u) * dot (cross u v) (cross u v)
      = -dot (cross w u) (cross u v) * dot (cross u v) (cross v w)
        + (triple u v w) ^ 2 * dot u v := by
  rw [polar_inner_uv u v w hw, polar_self_ww u v hu hv,
      polar_inner_vw u v w hu, polar_inner_wu u v w hv]
  linear_combination dual_spherical_law_cleared u v w hu hv hw

end SphericalLawOfCosinesOQ03
