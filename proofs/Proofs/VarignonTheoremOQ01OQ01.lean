/-
Proof: The signed-area law for the Varignon parallelogram.
Research: varignon-theorem-oq-01-oq-01

Open question (parent `varignon-theorem-oq-01`, first open question):
  "What is the relationship between the Varignon parallelogram's area and the
   original quadrilateral's area in the *self-intersecting* case?"

The parent file proves the affine skeleton of Varignon's theorem — the midpoints
of the sides of any quadrilateral form a parallelogram — using only the midpoint
structure.  That argument never mentions area, and it is silent on the classical
"half the area" statement, which is usually proved for *convex* quadrilaterals by
a picture.  The picture breaks for self-intersecting (crossed) quadrilaterals.

This file resolves the question by replacing area-by-picture with the **signed**
shoelace area, which is a polynomial in the coordinates and therefore makes no
distinction between convex, concave, and self-intersecting quadrilaterals.  We
prove, as a single ring identity in the eight coordinates of `A, B, C, D`:

  * **Diagonal form of the quadrilateral area.**
      `signedArea A B C D = cross (C - A) (D - B) / 2`,
    i.e. the signed area depends only on the two diagonals `AC` and `BD`.
  * **Diagonal form of the Varignon area.**
      `varignonArea A B C D = cross (C - A) (D - B) / 4`.
  * **The half-area law (headline).**
      `varignonArea A B C D = signedArea A B C D / 2`,
    valid for *every* quadrilateral, with no convexity or simplicity hypothesis.

Because the statements are identities of real polynomials, the self-intersecting
case is not a separate case at all — it is the same identity.  We exhibit a
crossed quadrilateral with *negative* signed area to show the law is genuinely
signed (the unsigned "half the area" slogan would be false there, but the signed
law holds exactly).

Conventions match the parent (`Point := ℝ × ℝ`, `midpoint2` the componentwise
average); `signedArea`/`cross` are declared self-containedly so the entry
compiles without the parent's olean.
-/

import Mathlib.Tactic

namespace VarignonArea

/-- A point of the plane, modeled as a pair of real coordinates (matches the
parent `VarignonTheorem.Point`). -/
abbrev Point := ℝ × ℝ

/-- The midpoint of two points (the componentwise average), as in the parent. -/
noncomputable def midpoint2 (X Y : Point) : Point :=
  ((X.1 + Y.1) / 2, (X.2 + Y.2) / 2)

/-- The 2-D cross product (the `z`-component of the 3-D cross product, a.k.a. the
wedge / signed parallelogram area of two vectors):
`cross U V = U.x · V.y − U.y · V.x`. -/
def cross (U V : Point) : ℝ := U.1 * V.2 - U.2 * V.1

/-- Vector difference of two points. -/
def sub2 (X Y : Point) : Point := (X.1 - Y.1, X.2 - Y.2)

/-- The **signed area** of the quadrilateral `A → B → C → D` via the shoelace
formula.  Unlike the unsigned area this is a polynomial in the coordinates, so it
is defined uniformly for convex, concave, and self-intersecting quadrilaterals
(the sign records orientation, and is negative for a clockwise traversal). -/
noncomputable def signedArea (A B C D : Point) : ℝ :=
  (cross A B + cross B C + cross C D + cross D A) / 2

/-- The **signed area of the Varignon parallelogram** `PQRS`, where
`P = mid(A,B)`, `Q = mid(B,C)`, `R = mid(C,D)`, `S = mid(D,A)`. -/
noncomputable def varignonArea (A B C D : Point) : ℝ :=
  signedArea (midpoint2 A B) (midpoint2 B C) (midpoint2 C D) (midpoint2 D A)

/-- **The quadrilateral's signed area depends only on its diagonals.**
For any quadrilateral `ABCD`, the shoelace area equals half the cross product of
the diagonal vectors `AC = C − A` and `BD = D − B`:
`signedArea A B C D = cross (C − A) (D − B) / 2`.  This is the key reformulation
that makes the self-intersecting case automatic. -/
theorem signedArea_eq_half_cross_diagonals (A B C D : Point) :
    signedArea A B C D = cross (sub2 C A) (sub2 D B) / 2 := by
  simp only [signedArea, cross, sub2]
  ring

/-- **The Varignon parallelogram's signed area is a quarter of the diagonal
cross product.**  Its sides are the half-diagonals `(C − A)/2` and `(D − B)/2`,
so its signed area is `cross (C − A) (D − B) / 4`. -/
theorem varignonArea_eq_quarter_cross_diagonals (A B C D : Point) :
    varignonArea A B C D = cross (sub2 C A) (sub2 D B) / 4 := by
  simp only [varignonArea, signedArea, varignonArea, midpoint2, cross, sub2]
  ring

/-- **Varignon's area law (headline).**  The Varignon parallelogram has exactly
half the signed area of the original quadrilateral:
`varignonArea A B C D = signedArea A B C D / 2`.

This is a polynomial identity in the eight coordinates, so it holds with **no**
convexity or simplicity hypothesis — in particular it answers the parent's open
question by covering the self-intersecting case on the same footing as the convex
one. -/
theorem varignonArea_eq_half_signedArea (A B C D : Point) :
    varignonArea A B C D = signedArea A B C D / 2 := by
  rw [varignonArea_eq_quarter_cross_diagonals, signedArea_eq_half_cross_diagonals]
  ring

/-- Equivalent multiplicative phrasing: twice the Varignon area equals the
quadrilateral area, `2 · varignonArea = signedArea`. -/
theorem two_mul_varignonArea (A B C D : Point) :
    2 * varignonArea A B C D = signedArea A B C D := by
  rw [varignonArea_eq_half_signedArea]; ring

/-- **The Varignon parallelogram is never collapsed unless the diagonals are
parallel.**  Its signed area vanishes exactly when the diagonal cross product
does, i.e. when `AC ∥ BD`. -/
theorem varignonArea_eq_zero_iff (A B C D : Point) :
    varignonArea A B C D = 0 ↔ cross (sub2 C A) (sub2 D B) = 0 := by
  rw [varignonArea_eq_quarter_cross_diagonals]
  constructor
  · intro h; linarith [h]
  · intro h; rw [h]; ring

/-! ### Self-intersecting witness

A *crossed* (self-intersecting) quadrilateral, traversed `A → B → C → D` so that
edges `BC` and `DA` cross.  Its signed shoelace area is **negative**, so the
naive unsigned "half the area" slogan is ambiguous there, yet the signed law
`varignonArea = signedArea / 2` holds exactly. -/

/-- Vertices of a self-intersecting quadrilateral: with the order
`(0,0) → (0,3) → (3,0) → (3,1)` the edges `BC` (from `(0,3)` to `(3,0)`) and `DA`
(from `(3,1)` to `(0,0)`) cross at `(9/4, 3/4)`. -/
def Ax : Point := (0, 0)
def Bx : Point := (0, 3)
def Cx : Point := (3, 0)
def Dx : Point := (3, 1)

/-- The crossed quadrilateral has **negative** signed area (clockwise net
orientation): the unsigned-area picture proof cannot apply, only the signed
identity. -/
theorem crossed_signedArea_neg : signedArea Ax Bx Cx Dx = -3 := by
  simp only [signedArea, cross, Ax, Bx, Cx, Dx]; norm_num

/-- Even for that crossed quadrilateral the half-area law holds on the nose:
`varignonArea = signedArea / 2 = -3/2`. -/
theorem crossed_varignonArea : varignonArea Ax Bx Cx Dx = -3 / 2 := by
  rw [varignonArea_eq_half_signedArea, crossed_signedArea_neg]

end VarignonArea
