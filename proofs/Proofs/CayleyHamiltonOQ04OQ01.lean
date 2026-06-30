import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-
# Explicit 3×3 Cayley–Hamilton in Trace / Principal-Minor / Determinant Form

## What This Proves
For an arbitrary 3×3 matrix `A` over a commutative ring `R`, the characteristic
polynomial is `X³ − (tr A)X² + c₂ X − det A`, where `c₂` is the sum of the three
2×2 principal minors of `A`. This file proves, *by direct entrywise computation*
(not the general `Matrix.aeval_self_charpoly` machinery):

1. **Explicit 3×3 Cayley–Hamilton**:
   `A³ − (tr A) • A² + c₂ • A − (det A) • 1 = 0`.
2. **Square/cube reductions**: rearranged forms expressing `A³` as a linear
   combination of `A²`, `A`, and `1`.

## Why This Is Not Just a Re-export
Mathlib's `Matrix.aeval_self_charpoly` states Cayley–Hamilton in terms of
`charpoly`, the determinant of `X • 1 − A`; it does *not* hand you the bare
identity `A³ − (tr A) • A² + c₂ • A − (det A) • 1 = 0` in trace / minor /
determinant form. The result here is proved from scratch by expanding
`Matrix.mul_apply` over `Fin 3` and closing with `ring`, so the file is
self-contained down to `ring`. It is the exact 3×3 analogue of the 2×2 identity
`A² − (tr A) • A + (det A) • 1 = 0` proved in `CayleyHamiltonOQ04.lean`, ported by
the same method as requested by open question OQ-04 of the Cayley–Hamilton entry.

## The middle coefficient `c₂`
For `A = (aᵢⱼ)`, the coefficient of `X` in the characteristic polynomial is the
sum of the 2×2 principal minors (the second elementary symmetric function of the
eigenvalues):
`c₂ = (a₀₀a₁₁ − a₀₁a₁₀) + (a₀₀a₂₂ − a₀₂a₂₀) + (a₁₁a₂₂ − a₁₂a₂₁)`.

## Mathematical Significance
The 3×3 case underlies spatial linear algebra: rotations in `ℝ³`, the inertia
tensor, and the cross-product/triple-product identities all live here. The
trace/minor/determinant coefficients are the three elementary symmetric
polynomials in the eigenvalues, so this identity is the degree-3 instance of the
Newton-style passage from power sums to the characteristic polynomial.

## Extends
- CayleyHamiltonOQ04.lean (Explicit 2×2 Cayley–Hamilton)
- CayleyHamilton.lean (Wiedijk #49)
- Open question OQ-04 of the Cayley–Hamilton entry (the explicit 3×3 analogue).

## Status
- [x] Complete proof (no sorries, no axioms)
-/

namespace CayleyHamiltonOQ04OQ01

open Matrix

variable {R : Type*} [CommRing R]

/-- The middle characteristic coefficient `c₂` of a 3×3 matrix: the sum of its
three 2×2 principal minors,
`(a₀₀a₁₁ − a₀₁a₁₀) + (a₀₀a₂₂ − a₀₂a₂₀) + (a₁₁a₂₂ − a₁₂a₂₁)`. This is the second
elementary symmetric function of the eigenvalues, i.e. the coefficient of `X` in
the characteristic polynomial `X³ − (tr A)X² + c₂X − det A`. -/
def c2 (A : Matrix (Fin 3) (Fin 3) R) : R :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0)
    + (A 0 0 * A 2 2 - A 0 2 * A 2 0)
    + (A 1 1 * A 2 2 - A 1 2 * A 2 1)

/-- **Explicit 3×3 Cayley–Hamilton.** Every 3×3 matrix satisfies its own
characteristic polynomial `X³ − (tr A)X² + c₂X − det A`, proved by direct
entrywise expansion over `Fin 3` and `ring`. -/
theorem cube_sub_trace_smul_sq_add_c2_smul_sub_det_smul
    (A : Matrix (Fin 3) (Fin 3) R) :
    A ^ 3 - A.trace • A ^ 2 + c2 A • A - A.det • 1 = 0 := by
  have h3 : A ^ 3 = A * A * A := by rw [pow_succ, pow_succ, pow_one]
  rw [h3, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
      Matrix.det_fin_three, c2, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.zero_apply] <;> ring

/-- A convenient restatement: `A³ = (tr A) • A² − c₂ • A + (det A) • 1`, expressing
the cube of any 3×3 matrix as a linear combination of `A²`, `A`, and the
identity. -/
theorem cube_eq (A : Matrix (Fin 3) (Fin 3) R) :
    A ^ 3 = A.trace • A ^ 2 - c2 A • A + A.det • 1 := by
  have h := cube_sub_trace_smul_sq_add_c2_smul_sub_det_smul A
  linear_combination (norm := module) h

end CayleyHamiltonOQ04OQ01
