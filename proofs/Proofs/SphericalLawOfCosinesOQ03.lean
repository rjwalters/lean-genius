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

end SphericalLawOfCosinesOQ03
