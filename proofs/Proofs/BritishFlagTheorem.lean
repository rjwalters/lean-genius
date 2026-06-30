import Mathlib.Tactic

/-!
# The British Flag Theorem

For any rectangle `ABCD` and any point `P` in the plane,
`|PA|² + |PC|² = |PB|² + |PD|²`, where the sum over one pair of opposite
corners equals the sum over the other pair.

We work in the coordinate plane `ℝ × ℝ` and measure squared Euclidean distance
explicitly via `sqDist`, rather than the ambient `Prod` metric (which is the
sup metric, not Euclidean). This keeps the statement unambiguous and the proof
`sorry`-free and axiom-free.

## Statement

A rectangle `ABCD` is encoded by structural hypotheses on the vertices:

* `hperp` : the sides `AB` and `AD` are perpendicular (right angle at `A`);
* `hpar1`, `hpar2` : `ABCD` closes up as a parallelogram, `C = B + D - A`,
  stated coordinatewise.

Together these characterise a rectangle (a parallelogram with one right angle).
The conclusion holds for an arbitrary point `P`, with no nondegeneracy
assumption.

## Proof idea

Write `u = B - A`, `v = D - A`. Then `C = A + u + v`, and with `p = P - A`,
```
PA² + PC² = |p|² + |p - u - v|²,
PB² + PD² = |p - u|² + |p - v|².
```
Their difference collapses to `|u + v|² - |u|² - |v|² = 2 (u ⬝ v) = 0`,
using only the perpendicularity hypothesis. The whole identity is therefore a
single polynomial consequence of `hperp`.
-/

namespace BritishFlagTheorem

/-- Squared Euclidean distance between two points of the coordinate plane. -/
def sqDist (P Q : ℝ × ℝ) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/--
**British Flag Theorem.**
If `ABCD` is a rectangle — sides `AB ⊥ AD` (`hperp`) and the parallelogram
closing condition `C = B + D - A` (`hpar1`, `hpar2`) — then for any point `P`,
`sqDist P A + sqDist P C = sqDist P B + sqDist P D`.
-/
theorem british_flag
    (A B C D P : ℝ × ℝ)
    (hperp : (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0)
    (hpar1 : C.1 = B.1 + D.1 - A.1)
    (hpar2 : C.2 = B.2 + D.2 - A.2) :
    sqDist P A + sqDist P C = sqDist P B + sqDist P D := by
  simp only [sqDist]
  rw [hpar1, hpar2]
  linear_combination 2 * hperp

end BritishFlagTheorem
