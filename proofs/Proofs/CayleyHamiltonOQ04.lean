import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-
# Explicit 2×2 Cayley–Hamilton and the Adjugate Inverse Formula

## What This Proves
For an arbitrary 2×2 matrix `A = !![a, b; c, d]` over a commutative ring `R`, everything
about its characteristic polynomial, adjugate, and inverse can be written down in closed
form. This file proves, *by direct entrywise computation* (not the general Cayley–Hamilton
or Laplace-expansion machinery):

1. **Explicit Cayley–Hamilton**: `A² − (tr A) • A + (det A) • 1 = 0`, i.e. every 2×2
   matrix annihilates its own characteristic polynomial `X² − (tr A)X + det A`.
2. **Explicit adjugate product**: `A * !![d, -b; -c, a] = (det A) • 1` and symmetrically
   `!![d, -b; -c, a] * A = (det A) • 1`, where `!![d, -b; -c, a]` is the classical 2×2
   adjugate (cofactor) matrix.
3. **Inverse formula over a field**: if `det A ≠ 0` then
   `A⁻¹ = (det A)⁻¹ • !![d, -b; -c, a]`, and this is a genuine two-sided inverse.

## Why This Is Not Just a Re-export
Mathlib's `Matrix.aeval_self_charpoly` states Cayley–Hamilton in terms of `charpoly`, a
polynomial built from the determinant of `X • 1 − A`; it does *not* hand you the bare
identity `A² − (tr A) • A + (det A) • 1 = 0` in trace/determinant form. Results (1) and (2)
here are proved from scratch by expanding `Matrix.mul_apply` over `Fin 2` and closing with
`ring`, so the file is self-contained down to `ring`. Result (3) then bridges these explicit
identities to Mathlib's `Matrix.inv_def`, giving the familiar `1/(ad−bc) · [[d,-b],[-c,a]]`.

## Mathematical Significance
The 2×2 case is the workhorse of planar linear algebra: rotations, shears, the Jacobian of a
two-variable change of coordinates, and Möbius transformations all reduce to these formulas.
The closed form `A⁻¹ = 1/(ad−bc) · [[d,-b],[-c,a]]` is the first nontrivial instance of
Cramer's rule and of the adjugate inverse `A⁻¹ = (det A)⁻¹ adj A`.

## Extends
- CayleyHamilton.lean (Wiedijk #49)
- Open question OQ-04 of the Cayley–Hamilton entry.

## Status
- [x] Complete proof (no sorries, no axioms)
-/

namespace CayleyHamiltonOQ04

open Matrix

variable {R : Type*} [CommRing R]

/-- The classical 2×2 adjugate (cofactor) matrix of `A = !![a,b;c,d]`, namely
`!![d, -b; -c, a]`. We give it a name so the explicit results below read like the
textbook formulas. This agrees with Mathlib's `Matrix.adjugate` (see
`cofactor_eq_adjugate`). -/
def cofactor (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![A 1 1, -A 0 1; -A 1 0, A 0 0]

/-- The hand-written `cofactor` matrix is exactly Mathlib's `adjugate` in the 2×2 case. -/
theorem cofactor_eq_adjugate (A : Matrix (Fin 2) (Fin 2) R) :
    cofactor A = adjugate A := by
  rw [cofactor, adjugate_fin_two]

/-- **Explicit 2×2 Cayley–Hamilton.** Every 2×2 matrix satisfies its own characteristic
polynomial `X² − (tr A)X + det A`, proved by direct entrywise expansion. -/
theorem sq_sub_trace_smul_add_det_smul (A : Matrix (Fin 2) (Fin 2) R) :
    A ^ 2 - A.trace • A + A.det • 1 = 0 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply] <;> ring

/-- A convenient restatement: `A² = (tr A) • A − (det A) • 1`, expressing the square of any
2×2 matrix as a linear combination of `A` and the identity. -/
theorem sq_eq (A : Matrix (Fin 2) (Fin 2) R) :
    A ^ 2 = A.trace • A - A.det • 1 := by
  have h := sq_sub_trace_smul_add_det_smul A
  linear_combination (norm := module) h

/-- **Explicit adjugate product (right).** `A · !![d,-b;-c,a] = (det A) • 1`, proved by
direct entrywise computation. -/
theorem mul_cofactor (A : Matrix (Fin 2) (Fin 2) R) :
    A * cofactor A = A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.smul_apply] <;> ring

/-- **Explicit adjugate product (left).** `!![d,-b;-c,a] · A = (det A) • 1`. -/
theorem cofactor_mul (A : Matrix (Fin 2) (Fin 2) R) :
    cofactor A * A = A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.smul_apply] <;> ring

section Field

variable {K : Type*} [Field K]

/-- **Inverse formula over a field.** The inverse is the scaled cofactor matrix
`A⁻¹ = (det A)⁻¹ • !![d,-b;-c,a]`. (This identity holds for every `A`: when `det A = 0`,
both sides degenerate via Mathlib's `Ring.inverse`; the genuine two-sided inverse property
requires `det A ≠ 0`, see `mul_det_inv_smul_cofactor` below.) -/
theorem inv_eq_det_inv_smul_cofactor (A : Matrix (Fin 2) (Fin 2) K) :
    A⁻¹ = (A.det)⁻¹ • cofactor A := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', cofactor_eq_adjugate]

/-- The scaled cofactor matrix is a genuine *right* inverse: `A · ((det A)⁻¹ • adj A) = 1`. -/
theorem mul_det_inv_smul_cofactor (A : Matrix (Fin 2) (Fin 2) K) (h : A.det ≠ 0) :
    A * ((A.det)⁻¹ • cofactor A) = 1 := by
  rw [Matrix.mul_smul, mul_cofactor, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The scaled cofactor matrix is a genuine *left* inverse: `((det A)⁻¹ • adj A) · A = 1`. -/
theorem det_inv_smul_cofactor_mul (A : Matrix (Fin 2) (Fin 2) K) (h : A.det ≠ 0) :
    ((A.det)⁻¹ • cofactor A) * A = 1 := by
  rw [Matrix.smul_mul, cofactor_mul, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The fully explicit closed form of the inverse:
`A⁻¹ = (1/(ad − bc)) • !![d, -b; -c, a]`. -/
theorem inv_fin_two_explicit (A : Matrix (Fin 2) (Fin 2) K) :
    A⁻¹ = (A.det)⁻¹ • !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  rw [inv_eq_det_inv_smul_cofactor A, cofactor]

end Field

end CayleyHamiltonOQ04
