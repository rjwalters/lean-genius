import Mathlib.Tactic

/-!
# The Parallelogram Defect Identity (generalizing the British Flag Theorem)

The British Flag Theorem states that for a **rectangle** `ABCD` and any point `P`,
`|PA|² + |PC|² = |PB|² + |PD|²`. The right angle at `A` is essential: it is what
makes the two corner-sums equal.

This file removes the right-angle hypothesis and keeps only the parallelogram
closing condition `C = B + D − A`. The two corner-sums then differ by a fixed
**defect**

```
|PA|² + |PC|² − (|PB|² + |PD|²) = 2 (AB · AD),
```

where `AB = B − A`, `AD = D − A` and `·` is the planar dot product. The key
phenomena are:

* the defect does **not depend on the point `P`** — it is an affine invariant of
  the parallelogram alone;
* it equals `2 (AB · AD)`, twice the dot product of the two sides at `A`, i.e. it
  measures exactly how far the angle at `A` is from a right angle;
* it has the **intrinsic diagonal form** `(|AC|² − |BD|²) / 2`, a difference of
  the squared diagonals, with no reference to a base vertex;
* the British Flag equality holds (for any one `P`, equivalently for all `P`) **iff**
  the angle at `A` is right.

As in the gallery's `BritishFlagTheorem`, we work in the coordinate plane `ℝ × ℝ`
with an explicit squared Euclidean distance `sqDist` (the ambient `Prod` metric is
the sup metric, not Euclidean). Everything is `sorry`-free and axiom-free.
-/

namespace BritishFlagDefect

/-- Squared Euclidean distance between two points of the coordinate plane. -/
def sqDist (P Q : ℝ × ℝ) : ℝ :=
  (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

/-- Planar dot product `u · v = u₁v₁ + u₂v₂`. -/
def dot (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/--
**Parallelogram defect identity.**
For a parallelogram `ABCD` (closing condition `C = B + D − A`) and any point `P`,
the British Flag defect equals `2 (AB · AD)`, twice the dot product of the two
sides meeting at `A`. In particular it does not involve `P`.
-/
theorem defect_eq_inner
    (A B C D P : ℝ × ℝ)
    (hpar1 : C.1 = B.1 + D.1 - A.1)
    (hpar2 : C.2 = B.2 + D.2 - A.2) :
    sqDist P A + sqDist P C - (sqDist P B + sqDist P D)
      = 2 * dot (B.1 - A.1, B.2 - A.2) (D.1 - A.1, D.2 - A.2) := by
  simp only [sqDist, dot]
  rw [hpar1, hpar2]
  ring

/--
**Intrinsic diagonal form of the defect.**
For a parallelogram `ABCD`, the British Flag defect is half the difference of the
squared diagonals, `(|AC|² − |BD|²) / 2`. This form refers only to the two
diagonals `AC` and `BD`, with no preferred base vertex.
-/
theorem defect_eq_diagonals
    (A B C D P : ℝ × ℝ)
    (hpar1 : C.1 = B.1 + D.1 - A.1)
    (hpar2 : C.2 = B.2 + D.2 - A.2) :
    sqDist P A + sqDist P C - (sqDist P B + sqDist P D)
      = (sqDist A C - sqDist B D) / 2 := by
  simp only [sqDist]
  rw [hpar1, hpar2]
  ring

/--
**The defect is independent of the chosen point.**
For a parallelogram `ABCD`, the value `|PA|² + |PC|² − (|PB|² + |PD|²)` is the
same for every point `P` (here `P` and `Q`), so it is an invariant of the
parallelogram itself.
-/
theorem defect_indep_of_point
    (A B C D P Q : ℝ × ℝ)
    (hpar1 : C.1 = B.1 + D.1 - A.1)
    (hpar2 : C.2 = B.2 + D.2 - A.2) :
    sqDist P A + sqDist P C - (sqDist P B + sqDist P D)
      = sqDist Q A + sqDist Q C - (sqDist Q B + sqDist Q D) := by
  rw [defect_eq_inner A B C D P hpar1 hpar2, defect_eq_inner A B C D Q hpar1 hpar2]

/--
**British Flag Theorem, recovered.**
If in addition the angle at `A` is right (`AB · AD = 0`, written coordinatewise as
`hperp`), the defect vanishes and we recover the classical equality
`|PA|² + |PC|² = |PB|² + |PD|²` for an arbitrary point `P`.
-/
theorem british_flag
    (A B C D P : ℝ × ℝ)
    (hperp : (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0)
    (hpar1 : C.1 = B.1 + D.1 - A.1)
    (hpar2 : C.2 = B.2 + D.2 - A.2) :
    sqDist P A + sqDist P C = sqDist P B + sqDist P D := by
  have h := defect_eq_inner A B C D P hpar1 hpar2
  simp only [dot] at h
  rw [hperp] at h
  linarith

/--
**Sharp characterization.**
For a parallelogram `ABCD` and any point `P`, the British Flag equality
`|PA|² + |PC|² = |PB|² + |PD|²` holds **iff** the angle at `A` is right
(`AB · AD = 0`). Since the defect is `P`-independent, the equality holds for one
`P` exactly when it holds for all `P`.
-/
theorem british_flag_iff_perp
    (A B C D P : ℝ × ℝ)
    (hpar1 : C.1 = B.1 + D.1 - A.1)
    (hpar2 : C.2 = B.2 + D.2 - A.2) :
    (sqDist P A + sqDist P C = sqDist P B + sqDist P D)
      ↔ (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0 := by
  have h := defect_eq_inner A B C D P hpar1 hpar2
  simp only [dot] at h
  constructor
  · intro he
    have hd : sqDist P A + sqDist P C - (sqDist P B + sqDist P D) = 0 := by linarith
    rw [hd] at h
    linarith
  · intro hperp
    rw [hperp] at h
    linarith

end BritishFlagDefect
