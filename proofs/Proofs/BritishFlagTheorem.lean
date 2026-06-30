import Mathlib.Tactic

/-!
# The British Flag Theorem

For a rectangle `A B C D` and an arbitrary point `P` in the plane,
`PA² + PC² = PB² + PD²`, where `A` and `C` are opposite corners (and likewise
`B` and `D`).

We work in the coordinate plane `ℝ × ℝ` and encode "rectangle" by the two
defining conditions on the vertices:

* `hpar`  : the quadrilateral closes up as a parallelogram, `C = B + D - A`;
* `hperp` : there is a right angle at `A`, i.e. the edge vectors `B - A` and
  `D - A` are orthogonal.

The proof is purely algebraic. Writing `u = B - A`, `v = D - A`, the squared
distances expand so that

`(PA² + PC²) - (PB² + PD²) = 2 (u ⬝ v)`,

which vanishes exactly because of the right-angle hypothesis `hperp`. The
British Flag theorem is therefore the orthogonality condition in disguise.
-/

namespace BritishFlagTheorem

/-- A point of the Euclidean plane, modeled as a pair of real coordinates. -/
abbrev Pt := ℝ × ℝ

/-- Squared Euclidean distance between two planar points. -/
def sqDist (P Q : Pt) : ℝ := (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- **British Flag theorem.**

For a rectangle `A B C D` — encoded as a parallelogram (`hpar`: `C = B + D - A`)
with a right angle at `A` (`hperp`: `(B - A) ⬝ (D - A) = 0`) — and any point `P`,
the sums of squared distances to opposite corners agree:
`PA² + PC² = PB² + PD²`. -/
theorem british_flag (A B C D P : Pt)
    (hpar : C = (B.1 + D.1 - A.1, B.2 + D.2 - A.2))
    (hperp : (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0) :
    sqDist P A + sqDist P C = sqDist P B + sqDist P D := by
  subst hpar
  simp only [sqDist]
  linear_combination (2 : ℝ) * hperp

end BritishFlagTheorem
