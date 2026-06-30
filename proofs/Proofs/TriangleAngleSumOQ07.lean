import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Triangle Angle Sum — Degenerate (Collinear) Cases (oq-07)

## The Open Question

The parent entry `triangle-angle-sum` verifies the classical identity
`∠ABC + ∠BCA + ∠CAB = π` for a non-degenerate triangle (Mathlib's
`EuclideanGeometry.angle_add_angle_add_angle_eq_pi`, which requires two vertices
distinct from the third). One of its listed open questions asks:

> *How does Mathlib's unoriented angle handle degenerate cases (collinear points),
> and what is the angle sum for a "triangle" with collinear vertices?*

This file answers it precisely, with fully verified Lean (no `sorry`, no `axiom`).

## The Answer

For the unoriented angle `∠` (`EuclideanGeometry.angle`, valued in `[0, π]`):

1. **One vertex strictly between the other two** (the generic collinear case,
   `Sbtw ℝ A B C`): the middle angle is the straight angle `π` and the two end
   angles collapse to `0`, so the sum is **still `π`**. The Euclidean angle-sum
   identity therefore extends continuously to this degenerate configuration.
2. The same conclusion holds from the bare hypothesis `∠ A B C = π` (equivalent to
   strict betweenness, `angle_eq_pi_iff_sbtw`).
3. **All three vertices coincide**: every angle is `∠ A A A = π/2` (Mathlib's
   convention `angle_self_left : ∠ p₀ p₀ p = π/2`), so the sum is `3π/2 ≠ π`.
   This shows the degenerate angle sum is *not* universally `π` — the value `π`
   is special to the strictly-between collinear configuration.

So Mathlib's unoriented angle behaves cleanly on collinear inputs, and the
"triangle angle sum" survives the strictly-between degeneration but breaks at the
fully-coincident one.
-/

namespace TriangleAngleSumOQ07

open scoped EuclideanGeometry

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- **Degenerate triangle angle sum (abstract form).**
If the angle at `B` is the straight angle `π` (i.e. `B` lies strictly between `A`
and `C`), the two remaining angles vanish and the angle sum is still `π`. -/
theorem angle_sum_of_angle_eq_pi {A B C : P} (h : ∠ A B C = Real.pi) :
    ∠ A B C + ∠ B C A + ∠ C A B = Real.pi := by
  have hCA : ∠ B C A = 0 := by
    have hCBA : ∠ C B A = Real.pi := by rw [EuclideanGeometry.angle_comm]; exact h
    exact EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left hCBA
  have hAB : ∠ C A B = 0 := by
    have hBAC : ∠ B A C = 0 := EuclideanGeometry.angle_eq_zero_of_angle_eq_pi_left h
    rw [EuclideanGeometry.angle_comm]; exact hBAC
  rw [h, hCA, hAB]; ring

/-- **Degenerate triangle angle sum (betweenness form).**
If `B` lies strictly between `A` and `C` (a collinear "triangle" with `B` the middle
vertex), the unoriented interior angle sum equals `π` — the classical identity
persists through this degeneration. -/
theorem Sbtw.angle_sum_eq_pi {A B C : P} (h : Sbtw ℝ A B C) :
    ∠ A B C + ∠ B C A + ∠ C A B = Real.pi :=
  angle_sum_of_angle_eq_pi h.angle₁₂₃_eq_pi

/-- **Fully coincident degeneration.**
When all three vertices coincide, Mathlib's convention `∠ A A A = π/2` makes the
angle sum `3π/2`, not `π`. Hence the degenerate angle sum is not universally `π`:
the value `π` is special to the strictly-between collinear case above. -/
theorem angle_sum_self (A : P) :
    ∠ A A A + ∠ A A A + ∠ A A A = 3 * (Real.pi / 2) := by
  rw [EuclideanGeometry.angle_self_left]; ring

end TriangleAngleSumOQ07
