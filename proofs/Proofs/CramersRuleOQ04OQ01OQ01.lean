import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Cramer's rule OQ-04 → OQ-01 → OQ-01: the explicit Cramer solution

The parent `CramersRuleOQ04OQ01` packages the adjugate identity
`A · adj A = (det A)·I` and its determinant-form corollary
`adjugate_mulVec_solve : A·(adj A · b) = (det A)·b`, the *determinant form* of
Cramer's rule. Its open question OQ-01 asks to

> *formalize the explicit Cramer solution* `xᵢ = det(Aᵢ)/det A`,
> *where `Aᵢ` is `A` with column `i` replaced by `b`, as an equality over a*
> *field when `det A ≠ 0`, connecting `cramer_apply` to* `adjugate_mulVec_solve`.

This file closes the gap from the determinant-scaled solution to the **honest
scalar formula**. The bridge is `Matrix.cramer`: by `cramer_apply` its `i`-th
component is exactly `det(Aᵢ)`, and the same adjugate identity that powers
`adjugate_mulVec_solve` shows the `cramer` vector equals `(det A) • x` for any
solution `x` of `A x = b`. Dividing by the nonzero determinant gives the
classical formula. `0` axioms.

## Main results

* `det_smul_solution_eq_cramer` : for **any** commutative ring, if `A x = b`
  then `(det A) • x = cramer A b`; i.e. `(det A)·xᵢ = det(Aᵢ)`. No
  invertibility needed — this is the algebraic core.
* `cramer_solution` : over a field with `det A ≠ 0`, the explicit scalar
  formula `xᵢ = det(Aᵢ) / det A`.
* `cramer_solution_eq` : the full solution vector `x = fun i => det(Aᵢ)/det A`.
* `cramer_solution_unique` : over a field with `det A ≠ 0`, the system `A x = b`
  has the Cramer vector as its **unique** solution.
* `cramer_formula_isSolution` : the Cramer vector really solves `A x = b`.
-/

namespace CramersRuleOQ04OQ01OQ01

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {R : Type*} [CommRing R]

/-- **Algebraic core of Cramer's rule** (any commutative ring, no invertibility).
    If `x` solves `A x = b`, then scaling `x` by the determinant recovers the
    Cramer vector: `(det A) • x = cramer A b`. Componentwise this is
    `(det A) · xᵢ = det(Aᵢ)`, where `Aᵢ = A.updateCol i b`.

    Proof: `cramer A b = adj A · b` (`cramer_eq_adjugate_mulVec`); substitute
    `b = A x` and collapse `adj A · (A · x) = (adj A · A) · x = (det A • 1)·x`
    via the adjugate identity `adjugate_mul`. -/
theorem det_smul_solution_eq_cramer (A : Matrix n n R) (x b : n → R)
    (hx : A *ᵥ x = b) : A.det • x = cramer A b := by
  rw [cramer_eq_adjugate_mulVec, ← hx, mulVec_mulVec, adjugate_mul, smul_mulVec,
    one_mulVec]

/-- Scalar form of the algebraic core: `(det A) · xᵢ = det(Aᵢ)`. -/
theorem det_mul_solution_eq_det_updateCol (A : Matrix n n R) (x b : n → R)
    (hx : A *ᵥ x = b) (i : n) :
    A.det * x i = (A.updateCol i b).det := by
  have h := congrFun (det_smul_solution_eq_cramer A x b hx) i
  rwa [Pi.smul_apply, smul_eq_mul, cramer_apply] at h

end CommRing

section Field

variable {K : Type*} [Field K]

/-- **The explicit Cramer formula.** Over a field, if `A x = b` and `det A ≠ 0`,
    then each coordinate of the solution is
    `xᵢ = det(Aᵢ) / det A`, with `Aᵢ = A.updateCol i b`. -/
theorem cramer_solution (A : Matrix n n K) (x b : n → K) (i : n)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x i = (A.updateCol i b).det / A.det := by
  rw [eq_div_iff hdet, mul_comm]
  exact det_mul_solution_eq_det_updateCol A x b hx i

/-- The full solution vector in closed form: `x = fun i => det(Aᵢ) / det A`. -/
theorem cramer_solution_eq (A : Matrix n n K) (x b : n → K)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x = fun i => (A.updateCol i b).det / A.det :=
  funext fun i => cramer_solution A x b i hx hdet

/-- **Uniqueness.** Over a field with `det A ≠ 0`, any two solutions of
    `A x = b` coincide — so the Cramer vector is *the* solution. -/
theorem cramer_solution_unique (A : Matrix n n K) (x y b : n → K)
    (hx : A *ᵥ x = b) (hy : A *ᵥ y = b) (hdet : A.det ≠ 0) :
    x = y := by
  rw [cramer_solution_eq A x b hx hdet, cramer_solution_eq A y b hy hdet]

/-- The Cramer vector really is a solution: `A · (fun i => det(Aᵢ)/det A) = b`.
    Combined with `cramer_solution_unique` this gives existence *and* uniqueness.
    Proof: `A.det⁻¹ • cramer A b` is the formula, and `A · cramer A b =
    det A • b` (`mulVec_cramer`); cancel the nonzero scalar. -/
theorem cramer_formula_isSolution (A : Matrix n n K) (b : n → K)
    (hdet : A.det ≠ 0) :
    A *ᵥ (fun i => (A.updateCol i b).det / A.det) = b := by
  have hcr : (fun i => (A.updateCol i b).det / A.det)
      = A.det⁻¹ • cramer A b := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, cramer_apply, div_eq_inv_mul]
  rw [hcr, mulVec_smul, mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]

end Field

end CramersRuleOQ04OQ01OQ01
