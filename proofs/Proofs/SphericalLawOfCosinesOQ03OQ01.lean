/-
# Spherical Law of Cosines — OQ-03 · OQ-01: the Hyperbolic Dual Law of Cosines

Research file for OQ-01 of the gallery entry `spherical-law-of-cosines-oq-03`
(the dual / angles spherical law of cosines).

## The OPEN question

OQ-03's first open question asks:

> Does the same clear-radicals-then-ring strategy yield the hyperbolic dual
> law of cosines `cosh C = − cosh A · cosh B + sinh A · sinh B · cosh c`
> over a Lorentzian (Minkowski) inner-product structure, with the cross
> product replaced by its pseudo-Euclidean analogue?

## Answer: yes — but the correct identity keeps the *angles* circular

The strategy carries over essentially verbatim, with the Euclidean dot
product on `ℝ³` replaced by the **Lorentzian inner product** of signature
`(+, +, −)` and the cross product replaced by the **Lorentzian cross
product** `mcross`. The result it produces, however, is the *standard*
**second (dual) hyperbolic law of cosines**

  `cos C = − cos A · cos B + sin A · sin B · cosh c`,

NOT the literal formula quoted in the open question. The angle functions
remain **circular** (`cos`, `sin`), only the included *side* becomes
hyperbolic (`cos c ↦ cosh c`). This is forced by the geometry: a hyperbolic
triangle's interior angles are ordinary Euclidean angles in `[0, π]`, and
they are realised here as the angle between the two *spacelike* edge normals
`u ⊠ v`, `u ⊠ w` at a vertex — whose Lorentzian inner product is
`sinh b · sinh c · cos A` and whose Lorentzian norms are `sinh b`, `sinh c`,
giving a genuine `cos A` with `|cos A| ≤ 1`. Replacing `cos A` by `cosh A`
(as the quoted formula does) would require an unbounded angle and does not
correspond to the algebra the Minkowski structure produces. So the honest
answer is: *the strategy works, and the radical-free polynomial identity it
yields is the second hyperbolic law of cosines with circular angle terms.*

## Strategy: a radical-free, division-free formalisation (Minkowski)

Work with vectors in `ℝ^{2,1}` as a 3-field structure `V`, with the
Lorentzian inner product

  `mdot u v = u.x·v.x + u.y·v.y − u.z·v.z`        (z-axis timelike)

and the Lorentzian cross product `mcross u v`, the unique vector with
`mdot (mcross u v) w = det(u, v, w)`. For three points `u, v, w` on the
upper hyperboloid `{ mdot x x = −1, x.z > 0 }` (the model of `H²`), the side
"cosines" are the *negative* hyperbolic cosines

  `mdot v w = −cosh a`,  `mdot w u = −cosh b`,  `mdot u v = −cosh c`,

(reverse Cauchy–Schwarz: two future timelike unit vectors have `mdot ≤ −1`).
The Lorentzian Binet–Cauchy and Lagrange identities pick up a sign relative
to the Euclidean ones:

  `mdot (mcross a b) (mcross c d) = mdot a d · mdot b c − mdot a c · mdot b d`,
  `mdot (mcross a b) (mcross a b) = (mdot a b)² − mdot a a · mdot b b`,

so for hyperboloid points the edge normal `u ⊠ v` is **spacelike** with
`mdot (mcross u v) (mcross u v) = (mdot u v)² − 1 = cosh²c − 1 = sinh²c ≥ 0`,
and `[u v w]² = −Gram = 1 − ca² − cb² − cc² − 2·ca·cb·cc` (the cross term
`−2·ca·cb·cc` flips sign relative to the spherical `+2`). Substituting the
normal forms `cos A = (cb·cc + ca)/(sinh b·sinh c)`, `sin A = [u v w]/(sinh b·sinh c)`
and clearing the radicals `sinh a, sinh b, sinh c` turns the dual law into a
polynomial identity (`hyp_dual_poly`, by `ring`).

## Contents

* `mdot`, `mcross`, `mtriple`     — Lorentzian inner / cross / triple products
* `binet_cauchy`, `lagrange_identity`, `triple_sq` — the (sign-flipped) Gram algebra
* `dot_cross_left` / `dot_cross_right`             — `mcross u v ⊥ u, v`
* `reverse_cauchy_schwarz`        — future unit timelike vectors: `mdot u v ≤ −1`
* `sinhc_sq_nonneg`               — `sinh²c ≥ 0` for a hyperboloid edge
* `hyp_dual_poly`                 — algebraic heart of the hyperbolic dual law   (ring)
* `hyp_dual_law_cleared`          — cleared dual law for abstract normal-form data
* `hyp_dual_law_minkowski_cleared`— cleared dual law for a hyperboloid triangle
* `hyp_dual_law_trig`             — literal trig dual law `cos C = −cos A·cos B + sin A·sin B·cosh c`
* `cosA_num` / `cosB_num` / `cosC_num` — angle-cosine numerators as Binet–Cauchy
  inner products of edge normals
* `sinha_sq` / `sinhb_sq` / `sinhc_sq` — side-sine squares as Lagrange self-inner-products
* `hyp_dual_law_cross_product_form` — the dual law in pure Lorentzian cross-product form

Axioms: 0.  Sorries: 0.

NOTE (significance): this is a faithful Lorentzian port of the spherical
`SphericalLawOfCosinesOQ03`. The mathematical news is the *correction* of the
open question's tentative all-hyperbolic formula to the geometrically correct
`cos C = −cos A·cos B + sin A·sin B·cosh c`, together with the explicit
sign-flips of the Lorentzian Gram algebra (`−2·ca·cb·cc`, the spacelike
edge-normal norm `(mdot u v)² − 1`) and the reverse Cauchy–Schwarz
well-definedness of the side lengths.
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace SphericalLawOfCosinesOQ03OQ01

open Real

/-! ## Part I: Minkowski 3-vectors, Lorentzian dot and cross products -/

/-- A vector in `ℝ³`, carrying the Lorentzian form of signature `(+, +, −)`. -/
structure V where
  x : ℝ
  y : ℝ
  z : ℝ

/-- Lorentzian (Minkowski) inner product of signature `(+, +, −)`; the
`z`-axis is timelike. -/
def mdot (u v : V) : ℝ := u.x * v.x + u.y * v.y - u.z * v.z

/-- Lorentzian cross product on `ℝ^{2,1}`: the unique vector with
`mdot (mcross u v) w = det(u, v, w)`. Compared with the Euclidean cross
product, the timelike (`z`) component is negated. -/
def mcross (u v : V) : V :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, -(u.x * v.y - u.y * v.x)⟩

/-- Lorentzian scalar triple product `[u v w] = mdot u (mcross v w) = det(u, v, w)`. -/
def mtriple (u v w : V) : ℝ := mdot u (mcross v w)

theorem mdot_comm (u v : V) : mdot u v = mdot v u := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v
  simp only [mdot]; ring

/-! ## Part II: Lorentzian Binet–Cauchy and Gram identities (pure `ring`)

These are the pseudo-Euclidean analogues of the Euclidean identities; each
carries an overall sign flip coming from the timelike direction. -/

/-- **Lorentzian Binet–Cauchy identity**:
    `mdot (a × b) (c × d) = mdot a d · mdot b c − mdot a c · mdot b d`.
Note the swapped pairing relative to the Euclidean
`⟨a,c⟩⟨b,d⟩ − ⟨a,d⟩⟨b,c⟩`: the Lorentzian signature flips the overall sign. -/
theorem binet_cauchy (a b c d : V) :
    mdot (mcross a b) (mcross c d) = mdot a d * mdot b c - mdot a c * mdot b d := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨c1, c2, c3⟩ := c; obtain ⟨d1, d2, d3⟩ := d
  simp only [mdot, mcross]; ring

/-- **Lorentzian Lagrange identity**:
    `mdot (a × b) (a × b) = (mdot a b)² − mdot a a · mdot b b`.
The sign is flipped from the Euclidean `‖a‖²‖b‖² − ⟨a,b⟩²`; for two future
timelike unit vectors this makes `a × b` spacelike. -/
theorem lagrange_identity (a b : V) :
    mdot (mcross a b) (mcross a b) = mdot a b ^ 2 - mdot a a * mdot b b := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [mdot, mcross]; ring

/-- The Lorentzian cross product is `mdot`-orthogonal to its first factor. -/
theorem dot_cross_left (a b : V) : mdot (mcross a b) a = 0 := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [mdot, mcross]; ring

/-- The Lorentzian cross product is `mdot`-orthogonal to its second factor. -/
theorem dot_cross_right (a b : V) : mdot (mcross a b) b = 0 := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
  simp only [mdot, mcross]; ring

/-- The squared Lorentzian triple product equals `− Gram(u, v, w)`. The leading
minus sign (`det η = −1`) is the Lorentzian signature; the Gram polynomial is
identical to the Euclidean one. -/
theorem triple_sq (u v w : V) :
    (mtriple u v w) ^ 2 =
      -(mdot u u * mdot v v * mdot w w
        + 2 * mdot u v * mdot v w * mdot w u
        - mdot u u * mdot v w ^ 2
        - mdot v v * mdot w u ^ 2
        - mdot w w * mdot u v ^ 2) := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v; obtain ⟨w1, w2, w3⟩ := w
  simp only [mtriple, mdot, mcross]; ring

/-! ## Part III: Reverse Cauchy–Schwarz and well-definedness of the sides

On the upper hyperboloid `{ mdot x x = −1, x.z > 0 }` (the model of `H²`),
two points have `mdot ≤ −1`, so `−mdot u v = cosh c ≥ 1` defines a genuine
hyperbolic distance and the edge normals are spacelike (`sinh²c ≥ 0`). -/

/-- **Reverse Cauchy–Schwarz** for the Minkowski form. Two future-directed
unit timelike vectors (`mdot · · = −1`, positive timelike component) satisfy
`mdot u v ≤ −1`, so `cosh c := −mdot u v ≥ 1`. The certificate is the sum of
squares `(u.x − v.x)² + (u.y − v.y)² + (u.x·v.y − u.y·v.x)² ≥ 0`. -/
theorem reverse_cauchy_schwarz (u v : V)
    (hu : mdot u u = -1) (hv : mdot v v = -1)
    (huz : 0 < u.z) (hvz : 0 < v.z) :
    mdot u v ≤ -1 := by
  simp only [mdot] at hu hv ⊢
  nlinarith [sq_nonneg (u.x - v.x), sq_nonneg (u.y - v.y),
    sq_nonneg (u.x * v.y - u.y * v.x), mul_pos huz hvz,
    sq_nonneg (u.z * v.z - 1), sq_nonneg (u.x * v.x + u.y * v.y + 1),
    mul_pos (mul_pos huz hvz) (mul_pos huz hvz)]

/-- For a hyperboloid edge, the side-sine square `sinh²c = (mdot u v)² − 1` is
nonnegative (the edge normal `u ⊠ v` is spacelike). -/
theorem sinhc_sq_nonneg (u v : V)
    (hu : mdot u u = -1) (hv : mdot v v = -1)
    (huz : 0 < u.z) (hvz : 0 < v.z) :
    0 ≤ mdot u v ^ 2 - 1 := by
  have h := reverse_cauchy_schwarz u v hu hv huz hvz
  nlinarith [h]

/-! ## Part IV: The algebraic heart of the hyperbolic dual law -/

/-- **Polynomial identity underlying the hyperbolic dual law of cosines.**

For real side inner products `ca, cb, cc` (`= −cosh a, −cosh b, −cosh c`):

  `(cc + ca·cb)(cc² − 1) = −(ca + cb·cc)(cb + ca·cc) − (1 − ca² − cb² − cc² − 2·ca·cb·cc)·cc`.

The left factor `cc² − 1` is `sinh²c`, the last factor is the squared
Lorentzian triple product `[u v w]²` (`= −Gram`), and the bracketed sums are
the numerators of the normal-form angle cosines. Dividing through produces
the dual law. Compared with the spherical `dual_poly`, the cross term inside
the Gram is `−2·ca·cb·cc` and the included-side term carries an extra minus
sign — exactly the Lorentzian signature. -/
theorem hyp_dual_poly (ca cb cc : ℝ) :
    (cc + ca * cb) * (cc ^ 2 - 1) =
      -(ca + cb * cc) * (cb + ca * cc)
        - (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * cc := by
  ring

/-- **Hyperbolic dual law of cosines (cleared, abstract form).**

Given side inner products `ca, cb, cc`, the squared side sine `sc2 = cc² − 1`,
and a squared triple product `tp2 = 1 − ca² − cb² − cc² − 2·ca·cb·cc`,

  `(cc + ca·cb)·sc2 = −(ca + cb·cc)(cb + ca·cc) − tp2·cc`.

Dividing both sides by `sinh a · sinh b · sinh² c` and using
`cos A = (cb·cc + ca)/(sinh b · sinh c)`, `sin A = √tp2/(sinh b · sinh c)`,
etc. gives the trig dual law `cos C = −cos A·cos B + sin A·sin B·cosh c`. -/
theorem hyp_dual_law_cleared
    (ca cb cc sc2 tp2 : ℝ)
    (hsc : sc2 = cc ^ 2 - 1)
    (htp : tp2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) :
    (cc + ca * cb) * sc2 = -(ca + cb * cc) * (cb + ca * cc) - tp2 * cc := by
  rw [hsc, htp]; ring

/-! ## Part V: The geometric dual law for a hyperboloid triangle -/

/-- **Hyperbolic dual law of cosines** for a triangle given by points
`u, v, w` on the hyperboloid (`mdot u u = mdot v v = mdot w w = −1`), in
cleared (radical-free, division-free) form.

With side inner products `ca = mdot v w` (`= −cosh a`), `cb = mdot w u`,
`cc = mdot u v`, and Lorentzian triple product `[u v w]`:

  `(cc + ca·cb)·(cc² − 1) = −(ca + cb·cc)(cb + ca·cc) − [u v w]²·cc`.

Here `cc² − 1 = sinh²c` and `[u v w]² = sinh²A · sinh²b · sinh²c = −Gram`, so
dividing by `sinh a · sinh b · sinh² c` yields exactly

  `cos C = −cos A · cos B + sin A · sin B · cosh c`. -/
theorem hyp_dual_law_minkowski_cleared
    (u v w : V) (hu : mdot u u = -1) (hv : mdot v v = -1) (hw : mdot w w = -1) :
    (mdot u v + mdot v w * mdot w u) * (mdot u v ^ 2 - 1)
      = -(mdot v w + mdot w u * mdot u v) * (mdot w u + mdot v w * mdot u v)
        - (mtriple u v w) ^ 2 * mdot u v := by
  have htp := triple_sq u v w
  rw [hu, hv, hw] at htp
  rw [htp]; ring

/-! ## Part VI: The literal trigonometric dual law
`cos C = −cos A·cos B + sin A·sin B·cosh c` -/

/-- **Literal trigonometric hyperbolic dual law of cosines.**

From the angle cos/sin defining relations taken in *cleared product form*
(the first hyperbolic law of cosines solved for the angle, with denominators
cleared) plus the side-Pythagorean identity `shc² = chc² − 1`, the second
hyperbolic law of cosines holds as the literal equality

  `cos C = −cos A · cos B + sin A · sin B · cosh c`,

where `cha, chb, chc` are the side hyperbolic cosines, `sha, shb, shc` the side
hyperbolic sines, and `cA, cB, cC, sA, sB` the **circular** cosines/sines of
the interior angles.

Division-free route (no `field_simp`): the angle relations are posited cleared,
the common denominator `sha·shb·shc²` is removed once via `mul_right_cancel₀`,
and the goal closes by a single `linear_combination` against the polynomial
heart. The structure is identical to the spherical `dual_law_trig`; only the
included side becomes `cosh c` and the Gram cross term becomes `+2·cha·chb·chc`. -/
theorem hyp_dual_law_trig
    (cha chb chc sha shb shc cA cB cC sA sB : ℝ)
    (hsa : sha ≠ 0) (hsb : shb ≠ 0) (hsc : shc ≠ 0)
    (hshc2 : shc ^ 2 = chc ^ 2 - 1)
    (hcA : cA * (shb * shc) = chb * chc - cha)
    (hcB : cB * (sha * shc) = cha * chc - chb)
    (hcC : cC * (sha * shb) = cha * chb - chc)
    (hsAsB : sA * sB * (sha * shb * shc ^ 2)
        = 1 - cha ^ 2 - chb ^ 2 - chc ^ 2 + 2 * cha * chb * chc) :
    cC = -cA * cB + sA * sB * chc := by
  have hD : sha * shb * shc ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsa hsb) (pow_ne_zero 2 hsc)
  have hAB : cA * cB * (sha * shb * shc ^ 2) = (chb * chc - cha) * (cha * chc - chb) := by
    have h : cA * (shb * shc) * (cB * (sha * shc)) = (chb * chc - cha) * (cha * chc - chb) := by
      rw [hcA, hcB]
    linear_combination h
  have key : (cha * chb - chc) * shc ^ 2
      = -(chb * chc - cha) * (cha * chc - chb)
        + (1 - cha ^ 2 - chb ^ 2 - chc ^ 2 + 2 * cha * chb * chc) * chc := by
    rw [hshc2]; ring
  apply mul_right_cancel₀ hD
  linear_combination (shc ^ 2) * hcC + hAB - chc * hsAsB + key

/-! ## Part VII: Fully geometric Lorentzian cross-product form

Each angle-cosine numerator is a Lorentzian Binet–Cauchy inner product of two
edge normals, and each side-sine square is a Lorentzian Lagrange
self-inner-product. Substituting these recovers the dual law in **pure
Lorentzian cross-product form** (`hyp_dual_law_cross_product_form`), grounding
the posited normal forms of `hyp_dual_law_trig` in actual Minkowski geometry;
all proofs remain `ring`/`rw`-only (no division, no radicals). -/

/-- Angle `A` (at vertex `u`) numerator as a Lorentzian Binet–Cauchy inner
product of the two edge normals at `u`:
`mdot (u ⊠ v) (u ⊠ w) = mdot v w + mdot w u · mdot u v`
(`= cosh b·cosh c − cosh a = sinh b·sinh c·cos A`). -/
theorem cosA_num (u v w : V) (hu : mdot u u = -1) :
    mdot (mcross u v) (mcross u w) = mdot v w + mdot w u * mdot u v := by
  have h := binet_cauchy u v u w
  rw [h, hu, mdot_comm u w, mdot_comm v u]; ring

/-- Angle `B` (at vertex `v`) numerator as a Lorentzian Binet–Cauchy inner
product of the two edge normals at `v`:
`mdot (v ⊠ w) (v ⊠ u) = mdot w u + mdot v w · mdot u v`. -/
theorem cosB_num (u v w : V) (hv : mdot v v = -1) :
    mdot (mcross v w) (mcross v u) = mdot w u + mdot v w * mdot u v := by
  have h := binet_cauchy v w v u
  rw [h, hv, mdot_comm v u, mdot_comm w v]; ring

/-- Angle `C` (at vertex `w`) numerator as a Lorentzian Binet–Cauchy inner
product of the two edge normals at `w`:
`mdot (w ⊠ u) (w ⊠ v) = mdot u v + mdot v w · mdot w u`. -/
theorem cosC_num (u v w : V) (hw : mdot w w = -1) :
    mdot (mcross w u) (mcross w v) = mdot u v + mdot v w * mdot w u := by
  have h := binet_cauchy w u w v
  rw [h, hw, mdot_comm w v, mdot_comm u w]; ring

/-- Side `c` sine-square as a Lorentzian Lagrange self-inner-product:
`mdot (u ⊠ v) (u ⊠ v) = (mdot u v)² − 1 = cosh²c − 1 = sinh²c`. -/
theorem sinhc_sq (u v : V) (hu : mdot u u = -1) (hv : mdot v v = -1) :
    mdot (mcross u v) (mcross u v) = mdot u v ^ 2 - 1 := by
  rw [lagrange_identity u v, hu, hv]; ring

/-- Side `b` sine-square: `mdot (w ⊠ u) (w ⊠ u) = (mdot w u)² − 1 = sinh²b`. -/
theorem sinhb_sq (u w : V) (hw : mdot w w = -1) (hu : mdot u u = -1) :
    mdot (mcross w u) (mcross w u) = mdot w u ^ 2 - 1 := by
  rw [lagrange_identity w u, hw, hu]; ring

/-- Side `a` sine-square: `mdot (v ⊠ w) (v ⊠ w) = (mdot v w)² − 1 = sinh²a`. -/
theorem sinha_sq (v w : V) (hv : mdot v v = -1) (hw : mdot w w = -1) :
    mdot (mcross v w) (mcross v w) = mdot v w ^ 2 - 1 := by
  rw [lagrange_identity v w, hv, hw]; ring

/-- **Hyperbolic dual law of cosines, pure Lorentzian cross-product form.**

For a hyperboloid triangle `u, v, w`, the cleared dual law holds with every
angle-cosine numerator and side-sine square replaced by its Lorentzian
cross-product realisation:

  `mdot (w⊠u) (w⊠v) · mdot (u⊠v) (u⊠v)
     = −mdot (u⊠v) (u⊠w) · mdot (v⊠w) (v⊠u) − [u v w]² · mdot u v`.

Reading off the geometric meaning (`mdot (w⊠u) (w⊠v) = sinh a sinh b cos C`,
`mdot (u⊠v) (u⊠v) = sinh²c`, `[u v w]² = sinh²A sinh²b sinh²c`, etc.) and
dividing by the positive product of side sines recovers
`cos C = −cos A cos B + sin A sin B cosh c`. Proved by rewriting the four
cross-product quantities to their side-inner-product normal forms
(`cosC_num`/`sinhc_sq`/`cosA_num`/`cosB_num`) and invoking
`hyp_dual_law_minkowski_cleared`. -/
theorem hyp_dual_law_cross_product_form
    (u v w : V) (hu : mdot u u = -1) (hv : mdot v v = -1) (hw : mdot w w = -1) :
    mdot (mcross w u) (mcross w v) * mdot (mcross u v) (mcross u v)
      = -(mdot (mcross u v) (mcross u w)) * mdot (mcross v w) (mcross v u)
        - (mtriple u v w) ^ 2 * mdot u v := by
  rw [cosC_num u v w hw, sinhc_sq u v hu hv, cosA_num u v w hu, cosB_num u v w hv]
  exact hyp_dual_law_minkowski_cleared u v w hu hv hw

end SphericalLawOfCosinesOQ03OQ01
