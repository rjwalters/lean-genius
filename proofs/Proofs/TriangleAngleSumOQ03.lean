import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Triangle Angle Sum: Mathlib Angle Function Degenerate Cases (OQ-03)

## Surprising Mathlib Fact

The Mathlib theorem `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` has signature:
```
theorem angle_add_angle_add_angle_eq_pi {p₁ p₂ : P} (p₃ : P) (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = π
```

Only ONE non-degeneracy condition is needed: `p₂ ≠ p₁`. The point `p₃` is unrestricted.
This means the gallery's `triangle_angle_sum` theorem carried an **unnecessary** hypothesis
`h₃ : p₃ ≠ p₁` — the result holds even when `p₃ = p₁`.

## Complete Degenerate Case Analysis

The angle sum equals π for **all configurations except one**:
- `p₂ ≠ p₁`: sum = π (for any p₃, including p₃ = p₁ or p₃ = p₂)
- `p₂ = p₁` and `p₃ ≠ p₁`: sum = π (angles are π/2, 0, π/2)
- `p₂ = p₁` and `p₃ = p₁`: sum = 3π/2 (every angle is π/2 by Mathlib convention)

**The only exceptional case**: when all three named points are equal.

## Mathlib Conventions for Degenerate Angles

Key `@[simp]` lemmas in `EuclideanGeometry`:
- `angle_self_left (p₀ p : P) : ∠ p₀ p₀ p = π / 2`
  (first arg = vertex: left vsub is zero → `arccos(0/0) = arccos(0) = π/2`)
- `angle_self_right (p₀ p : P) : ∠ p p₀ p₀ = π / 2`
  (third arg = vertex: right vsub is zero → `arccos(0/0) = arccos(0) = π/2`)
- `angle_self_of_ne (h : p ≠ p₀) : ∠ p p₀ p = 0`
  (first = third ≠ vertex: same direction → `arccos(1) = 0`)

## Status
- 0 sorries, 0 axioms
-/

namespace TriangleAngleSumOQ03

open scoped EuclideanGeometry
open Classical

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-! ## The Redundant Hypothesis

The `triangle_angle_sum` theorem in the parent file required `h₃ : p₃ ≠ p₁`.
This was unnecessary: the Mathlib theorem works for any `p₃`. -/

/-- The angle sum formula holds whenever `p₂ ≠ p₁`, for **any** choice of `p₃`.
    This is a direct corollary of the Mathlib theorem, using only one non-degeneracy condition.
    Compare: `TriangleAngleSum.triangle_angle_sum` required both `p₂ ≠ p₁` AND `p₃ ≠ p₁`. -/
theorem triangle_angle_sum_one_cond {p₁ p₂ p₃ : P} (h : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi p₃ h

/-! ## The Only Truly Degenerate Case: p₂ = p₁ with p₃ ≠ p₁ -/

/-- When `p₂ = p₁` but `p₃ ≠ p₁`, the angle sum is still π.
    The angles compute as π/2, 0, π/2 respectively.

    Note: this is NOT covered by `angle_add_angle_add_angle_eq_pi` since `p₂ = p₁`. -/
theorem triangle_angle_sum_p2_eq_p1 {p₁ p₂ p₃ : P}
    (h₂ : p₂ = p₁) (h₃ : p₃ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi := by
  have hself : ∠ p₁ p₃ p₁ = 0 := EuclideanGeometry.angle_self_of_ne h₃.symm
  simp only [h₂, EuclideanGeometry.angle_self_left, EuclideanGeometry.angle_self_right,
             hself, zero_add, add_zero]
  linarith [Real.pi_pos]

/-! ## Fully Degenerate Case -/

/-- When all three points coincide (`p₂ = p₁` and `p₃ = p₁`), the angle sum is 3π/2.
    Each angle equals π/2 by Mathlib's convention `arccos(0/0) = π/2`.
    This is the ONLY case where the angle sum formula fails. -/
theorem triangle_angle_sum_fully_degenerate {p₁ p₂ p₃ : P}
    (h₂ : p₂ = p₁) (h₃ : p₃ = p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = 3 * Real.pi / 2 := by
  simp only [h₂, h₃]
  linarith [EuclideanGeometry.angle_self_left p₁ p₁, Real.pi_pos]

/-- Every angle of a fully degenerate "triangle" is π/2. -/
theorem angle_self_self_self (p : P) : ∠ p p p = Real.pi / 2 :=
  EuclideanGeometry.angle_self_left p p

/-! ## Complete Characterization -/

/-- **Main Result**: The angle sum formula holds if and only if NOT BOTH `p₂ = p₁` AND `p₃ = p₁`.

In other words:
- The formula ALWAYS holds when `p₂ ≠ p₁` (for any `p₃`)
- The formula HOLDS when `p₂ = p₁` but `p₃ ≠ p₁` (angles: π/2, 0, π/2)
- The formula FAILS when `p₂ = p₁` and `p₃ = p₁` (sum = 3π/2, not π)

The necessary and sufficient condition for sum = π is: at least one of {p₂ ≠ p₁, p₃ ≠ p₁} holds. -/
theorem triangle_angle_sum_iff_not_fully_degenerate {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi ↔ ¬(p₂ = p₁ ∧ p₃ = p₁) := by
  constructor
  · intro hsum ⟨h₂, h₃⟩
    have hfd := triangle_angle_sum_fully_degenerate h₂ h₃
    linarith [Real.pi_pos]
  · intro hne
    by_cases h₂ : p₂ = p₁
    · have h₃ : p₃ ≠ p₁ := fun h₃ => hne ⟨h₂, h₃⟩
      exact triangle_angle_sum_p2_eq_p1 h₂ h₃
    · exact EuclideanGeometry.angle_add_angle_add_angle_eq_pi p₃ h₂

/-! ## Unconditional Formula -/

/-- The angle sum, stated unconditionally.
    The sum is π for all non-degenerate inputs, and 3π/2 only when all three points are equal. -/
theorem triangle_angle_sum_unconditional {p₁ p₂ p₃ : P} :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ =
      if p₂ = p₁ ∧ p₃ = p₁ then 3 * Real.pi / 2 else Real.pi := by
  rcases Classical.em (p₂ = p₁ ∧ p₃ = p₁) with ⟨h₂, h₃⟩ | h
  · rw [if_pos ⟨h₂, h₃⟩]
    exact triangle_angle_sum_fully_degenerate h₂ h₃
  · rw [if_neg h]
    exact triangle_angle_sum_iff_not_fully_degenerate.mpr h

/-! ## Concrete Verification -/

-- ∠ p p p = π/2 for any point p (degenerate self-angle)
example (p : EuclideanSpace ℝ (Fin 2)) : ∠ p p p = Real.pi / 2 :=
  EuclideanGeometry.angle_self_left p p

-- Degenerate case: p₂ = p₁ with p₃ distinct still gives π
example : ∀ (p₁ p₃ : EuclideanSpace ℝ (Fin 2)), p₃ ≠ p₁ →
    ∠ p₁ p₁ p₃ + ∠ p₁ p₃ p₁ + ∠ p₃ p₁ p₁ = Real.pi := fun _ _ h =>
  triangle_angle_sum_p2_eq_p1 rfl h

end TriangleAngleSumOQ03
