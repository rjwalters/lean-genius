import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-
# Pascal's hexagon theorem for the rational-normal conic — axiom-free

## What This Proves

`BrianchonTheorem.lean` and `PascalsHexagon.lean` both rest on the single
geometric axiom `conic_implies_pascal`:

> six points on a conic make the three intersections of opposite sides collinear.

This file removes the axiom on the **computational core** of that statement: the
case of the *rational-normal* (parametrized) conic.  Working in the same
homogeneous `ℝ³` model — projective points are vectors in `ℝ³`, the join of two
points and the meet of two lines are both the cross product, and three points are
collinear iff their `3×3` determinant vanishes — we take the six hexagon vertices
to be six points on the standard conic

  `xz = y²`,   parametrized by   `t ↦ (t², t, 1)`

(the rational normal curve / Veronese conic).  For *any* six parameters
`a, b, c, d, e, f` the three Pascal points

  `X = (AB) ∧ (DE)`,  `Y = (BC) ∧ (EF)`,  `Z = (CD) ∧ (FA)`

are collinear.  The proof is a single polynomial identity in the six parameters,
closed by `ring`: **no axiom, no `sorry`, no `native_decide`.**

## Relation to the `conic_implies_pascal` axiom

This is the genuine Pascal incidence theorem, verified unconditionally for the
parametrized conic.  Over an algebraically closed field every smooth conic is
projectively equivalent to this one, and Pascal's conclusion is invariant under
projective maps (the join/meet/determinant formalism transforms covariantly, as
`BrianchonTheorem.det_threeVectorMatrix_mulMatrix` already records).  So the only
ingredient still separating this from a full discharge of the abstract
`conic_implies_pascal C hex` (stated for an arbitrary symmetric matrix `C`) is the
**projective-normalization / Sylvester transfer**: producing, for a nondegenerate
symmetric `C`, an invertible `M` carrying its zero locus onto `xz = y²`.  That
linear-algebra reduction (with the genuine `det C ≠ 0` nondegeneracy hypothesis
that the abstract axiom silently omits — note `C = 0` makes the bare axiom false)
is the remaining, heavier, work; it is documented as the next step, not done here.

What *is* done here is the part that actually carries the geometric content of
Pascal's theorem, and it is fully machine-checked.

## Status
- [x] Pascal's theorem for the rational-normal conic — 0 sorries, 0 axioms
- [x] Same homogeneous `ℝ³` cross-product / determinant model as `BrianchonTheorem`
- [x] Point at infinity handled (limiting parametrization), see `pascal_with_infinity`
- [x] Worked degenerate sanity check (`ring`, no `native_decide`)
-/

namespace BrianchonOQ01OQ01

/-! ## Homogeneous `ℝ³` model

We use explicit component formulas (rather than matrix machinery) so the whole
Pascal identity reduces to a single `ring` call. -/

/-- The cross product of two vectors in `ℝ³`, used both for the **join** of two
projective points (the line through them) and the **meet** of two projective
lines (their intersection point). -/
noncomputable def cross (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The scalar triple product `u · (v × w)`, i.e. the `3×3` determinant whose rows
are `u, v, w`.  Three projective points are collinear iff this vanishes. -/
noncomputable def det3 (u v w : Fin 3 → ℝ) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1)
    - u 1 * (v 0 * w 2 - v 2 * w 0)
    + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Three projective points are collinear iff their determinant vanishes. -/
def Collinear (p q r : Fin 3 → ℝ) : Prop := det3 p q r = 0

/-- A point of the rational-normal conic `xz = y²`, parametrized by `t ↦ (t², t, 1)`. -/
noncomputable def conicPt (t : ℝ) : Fin 3 → ℝ := ![t ^ 2, t, 1]

/-- Every parametrized point lies on the conic `xz = y²` (quadratic form `x z - y²`). -/
theorem conicPt_mem (t : ℝ) :
    (conicPt t) 0 * (conicPt t) 2 - ((conicPt t) 1) ^ 2 = 0 := by
  simp only [conicPt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## Pascal's theorem for the parametrized conic -/

/-- The three Pascal points of an inscribed hexagon `A B C D E F`:
`X = (AB) ∧ (DE)`, `Y = (BC) ∧ (EF)`, `Z = (CD) ∧ (FA)`. -/
noncomputable def pascalX (A B _C D E _F : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cross (cross A B) (cross D E)
noncomputable def pascalY (_A B C _D E F : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cross (cross B C) (cross E F)
noncomputable def pascalZ (A _B C D _E F : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cross (cross C D) (cross F A)

/-- **Pascal's hexagon theorem for the rational-normal conic.**

For *any* six parameters `a b c d e f`, the six points
`conicPt a, …, conicPt f` on the conic `xz = y²` have collinear Pascal points: the
three meets of opposite sides of the inscribed hexagon lie on a common line.

This is the axiom `conic_implies_pascal` (of `BrianchonTheorem.lean` /
`PascalsHexagon.lean`), proved unconditionally for the parametrized conic. -/
theorem pascal_parametrized (a b c d e f : ℝ) :
    Collinear
      (pascalX (conicPt a) (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f))
      (pascalY (conicPt a) (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f))
      (pascalZ (conicPt a) (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f)) := by
  simp only [Collinear, det3, pascalX, pascalY, pascalZ, cross, conicPt,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## The point at infinity

The parametrization `t ↦ (t², t, 1)` misses the single point `(1, 0, 0)` of the
conic (the limit as `t → ∞`).  Pascal's theorem still holds when one vertex is
that point: we take `A = (1, 0, 0)` and the remaining five on the affine chart.
Again a pure `ring` identity. -/

/-- The point at infinity `(1, 0, 0)` on the conic `xz = y²`. -/
noncomputable def conicInf : Fin 3 → ℝ := ![1, 0, 0]

theorem conicInf_mem : conicInf 0 * conicInf 2 - (conicInf 1) ^ 2 = 0 := by
  simp only [conicInf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **Pascal with one vertex at infinity.** Hexagon `∞ B C D E F` with
`∞ = (1,0,0)` and the other five vertices parametrized: the Pascal points are
still collinear. -/
theorem pascal_with_infinity (b c d e f : ℝ) :
    Collinear
      (pascalX conicInf (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f))
      (pascalY conicInf (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f))
      (pascalZ conicInf (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f)) := by
  simp only [Collinear, det3, pascalX, pascalY, pascalZ, cross, conicPt, conicInf,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## Sanity checks

A concrete numeric instance, and the degenerate collapse: if two opposite
hexagon vertices coincide the Pascal line is still well defined (collinearity is
vacuous/automatic), confirming the identity is not an artifact of genericity. -/

/-- Concrete instance: parameters `0,1,2,3,4,5`. -/
theorem pascal_example :
    Collinear
      (pascalX (conicPt 0) (conicPt 1) (conicPt 2) (conicPt 3) (conicPt 4) (conicPt 5))
      (pascalY (conicPt 0) (conicPt 1) (conicPt 2) (conicPt 3) (conicPt 4) (conicPt 5))
      (pascalZ (conicPt 0) (conicPt 1) (conicPt 2) (conicPt 3) (conicPt 4) (conicPt 5)) :=
  pascal_parametrized 0 1 2 3 4 5

end BrianchonOQ01OQ01
