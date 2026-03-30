/-
# Ptolemy's Theorem via Complex Numbers

An alternative proof of Ptolemy's theorem using complex number algebra.
The key insight: Ptolemy's equality is a consequence of a simple algebraic
identity over ℂ combined with the complex triangle inequality.

## Algebraic Identity

For any four complex numbers z₁, z₂, z₃, z₄:
  (z₁ - z₃)(z₂ - z₄) = (z₁ - z₂)(z₃ - z₄) + (z₂ - z₃)(z₁ - z₄)

This is a pure ring identity, verifiable by expansion.

## Ptolemy's Inequality

Taking absolute values and applying the triangle inequality:
  |z₁ - z₃| · |z₂ - z₄| ≤ |z₁ - z₂| · |z₃ - z₄| + |z₂ - z₃| · |z₁ - z₄|

This holds for ANY four points in the plane, with equality iff they are
concyclic (on a common circle) in the correct order.

## References

- Needham, Visual Complex Analysis (1997), Chapter 6
- Aigner & Ziegler, Proofs from THE BOOK, Chapter 21
- <https://erdosproblems.com> (context for cyclic quadrilateral problems)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module

open Complex

/- ## Part 1: The Algebraic Identity -/

/-- The fundamental algebraic identity underlying Ptolemy's theorem.
    For any four elements of a commutative ring:
    (z₁ - z₃)(z₂ - z₄) = (z₁ - z₂)(z₃ - z₄) + (z₂ - z₃)(z₁ - z₄)

    This is a pure ring identity, proved by `ring`. -/
theorem ptolemy_algebraic_identity {R : Type*} [CommRing R] (z₁ z₂ z₃ z₄ : R) :
    (z₁ - z₃) * (z₂ - z₄) = (z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄) := by
  ring

/-- The same identity stated over ℂ for clarity. -/
theorem ptolemy_complex_identity (z₁ z₂ z₃ z₄ : ℂ) :
    (z₁ - z₃) * (z₂ - z₄) = (z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄) :=
  ptolemy_algebraic_identity z₁ z₂ z₃ z₄

/- ## Part 2: Ptolemy's Inequality -/

/-- **Ptolemy's Inequality** (complex-number proof).

    For any four complex numbers (equivalently, four points in the plane):
    |z₁ - z₃| · |z₂ - z₄| ≤ |z₁ - z₂| · |z₃ - z₄| + |z₂ - z₃| · |z₁ - z₄|

    Proof: from the algebraic identity, take absolute values.
    |LHS| = |(z₁-z₂)(z₃-z₄) + (z₂-z₃)(z₁-z₄)| ≤ |...| + |...|
    by the triangle inequality. Then |a·b| = |a|·|b| gives the result.

    Equality holds iff the four points are concyclic in order. -/
theorem ptolemy_inequality (z₁ z₂ z₃ z₄ : ℂ) :
    abs (z₁ - z₃) * abs (z₂ - z₄) ≤
      abs (z₁ - z₂) * abs (z₃ - z₄) + abs (z₂ - z₃) * abs (z₁ - z₄) := by
  -- LHS = |z₁ - z₃| · |z₂ - z₄| = |(z₁ - z₃)(z₂ - z₄)|
  rw [← map_mul, ptolemy_complex_identity]
  -- Now: |(..) + (..)| ≤ |..| + |..|
  calc abs ((z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄))
      ≤ abs ((z₁ - z₂) * (z₃ - z₄)) + abs ((z₂ - z₃) * (z₁ - z₄)) :=
        abs_add _ _
    _ = abs (z₁ - z₂) * abs (z₃ - z₄) + abs (z₂ - z₃) * abs (z₁ - z₄) := by
        rw [map_mul, map_mul]

/-- Ptolemy's inequality stated using `Complex.normSq` for computations. -/
theorem ptolemy_inequality_norm (z₁ z₂ z₃ z₄ : ℂ) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ ≤
      ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  -- Complex.abs and norm coincide
  simp only [Complex.norm_eq_abs]
  exact ptolemy_inequality z₁ z₂ z₃ z₄

/- ## Part 3: Connecting to Distance -/

/-- The complex-number Ptolemy inequality expressed as a statement about
    distances between points in ℝ². Points in ℝ² are identified with ℂ.

    dist(z₁,z₃) · dist(z₂,z₄) ≤ dist(z₁,z₂) · dist(z₃,z₄) + dist(z₂,z₃) · dist(z₁,z₄) -/
theorem ptolemy_inequality_dist (z₁ z₂ z₃ z₄ : ℂ) :
    dist z₁ z₃ * dist z₂ z₄ ≤
      dist z₁ z₂ * dist z₃ z₄ + dist z₂ z₃ * dist z₁ z₄ := by
  simp only [dist_eq_norm]
  exact ptolemy_inequality_norm z₁ z₂ z₃ z₄
