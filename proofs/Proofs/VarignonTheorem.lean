import Mathlib.Tactic

/-
# Varignon's Theorem

## What This Proves
The midpoints of the sides of an arbitrary quadrilateral `ABCD` form a
parallelogram (the *Varignon parallelogram*). In its strong form, each side of
this midpoint quadrilateral is parallel to a diagonal of `ABCD` and has half its
length.

## Historical Context
Pierre Varignon (1654–1722) published this result posthumously in 1731. It holds
for *any* quadrilateral — convex, concave, or even self-intersecting — and even
for non-planar (skew) quadrilaterals, because the proof uses only the affine
midpoint structure, never any metric or convexity hypothesis.

## Approach
Model points as pairs of real coordinates `ℝ × ℝ`. Write the four side midpoints
as
  P = mid(A,B),  Q = mid(B,C),  R = mid(C,D),  S = mid(D,A).
The key computation is purely algebraic:
  Q − P = (B+C)/2 − (A+B)/2 = (C − A)/2,
  R − S = (C+D)/2 − (D+A)/2 = (C − A)/2,
so Q − P = R − S = (C − A)/2. The common value being half the diagonal `AC`
gives both the parallelogram property (opposite sides equal as vectors) and the
strong form (the side equals half the diagonal). Each coordinate identity is
discharged by `ring`.
-/

namespace VarignonTheorem

/-- A point of the plane, modeled as a pair of real coordinates. -/
abbrev Point := ℝ × ℝ

/-- The midpoint of two points (the componentwise average). -/
noncomputable def midpoint2 (X Y : Point) : Point := ((X.1 + Y.1) / 2, (X.2 + Y.2) / 2)

/-- **Strong form (side `PQ`).** The side `PQ` of the Varignon parallelogram —
the segment between the midpoints of `AB` and `BC` — equals half the diagonal
`AC`, componentwise. -/
theorem varignon_PQ_eq_half_AC (A B C D : Point) :
    (midpoint2 B C).1 - (midpoint2 A B).1 = (C.1 - A.1) / 2 ∧
    (midpoint2 B C).2 - (midpoint2 A B).2 = (C.2 - A.2) / 2 := by
  refine ⟨?_, ?_⟩ <;> dsimp only [midpoint2] <;> ring

/-- **Strong form (side `SR`).** The opposite side `SR` — the segment between the
midpoints of `DA` and `CD` — also equals half the diagonal `AC`, componentwise. -/
theorem varignon_SR_eq_half_AC (A B C D : Point) :
    (midpoint2 C D).1 - (midpoint2 D A).1 = (C.1 - A.1) / 2 ∧
    (midpoint2 C D).2 - (midpoint2 D A).2 = (C.2 - A.2) / 2 := by
  refine ⟨?_, ?_⟩ <;> dsimp only [midpoint2] <;> ring

/-- **Varignon's theorem.** The midpoints `P = mid(A,B)`, `Q = mid(B,C)`,
`R = mid(C,D)`, `S = mid(D,A)` of the sides of any quadrilateral `ABCD` form a
parallelogram: the opposite side vectors `PQ` and `SR` are equal, i.e.
`Q − P = R − S` componentwise. -/
theorem varignon (A B C D : Point) :
    (midpoint2 B C).1 - (midpoint2 A B).1 = (midpoint2 C D).1 - (midpoint2 D A).1 ∧
    (midpoint2 B C).2 - (midpoint2 A B).2 = (midpoint2 C D).2 - (midpoint2 D A).2 := by
  refine ⟨?_, ?_⟩ <;> dsimp only [midpoint2] <;> ring

/-- The other pair of opposite sides is likewise equal: `P − S = Q − R`
componentwise, equal to half the diagonal `BD`. This confirms `PQRS` is a
parallelogram from the second pair of sides as well. -/
theorem varignon_PS_eq_QR (A B C D : Point) :
    (midpoint2 A B).1 - (midpoint2 D A).1 = (midpoint2 B C).1 - (midpoint2 C D).1 ∧
    (midpoint2 A B).2 - (midpoint2 D A).2 = (midpoint2 B C).2 - (midpoint2 C D).2 := by
  refine ⟨?_, ?_⟩ <;> dsimp only [midpoint2] <;> ring

end VarignonTheorem
