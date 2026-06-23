import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Cramer's Rule (Wiedijk #97)

## What This Proves
Cramer's Rule provides an explicit formula for solving systems of linear equations
when the coefficient matrix is invertible.

For a system of n linear equations in n unknowns **Ax = b**, if det(A) ≠ 0, then:

$$x_i = \frac{\det(A_i)}{\det(A)}$$

where $A_i$ is the matrix A with the i-th column replaced by b.

More generally (without requiring invertibility):
$$A \cdot \text{cramer}(A, b) = \det(A) \cdot b$$

## Approach
- **Foundation (from Mathlib):** We use `Matrix.mulVec_cramer` which proves that
  multiplying A by the Cramer solution vector gives det(A) • b.
- **Key Insight:** The Cramer map `A.cramer b` computes a vector where the i-th
  component is det(A with column i replaced by b). When det(A) is invertible,
  dividing by det(A) gives the unique solution.
- **Proof Techniques Demonstrated:** Matrix operations, determinants, linear algebra.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Matrix.cramer` : The Cramer linear map
- `Matrix.mulVec_cramer` : A * cramer(A, b) = det(A) • b
- `Matrix.cramer_apply` : cramer(A, b)_i = det(A with col i replaced by b)
- `Matrix.cramer_eq_adjugate_mulVec` : Relates Cramer to adjugate matrix

## Historical Note
Cramer's Rule is named after Gabriel Cramer (1704-1752), who published the
rule in his 1750 work "Introduction to the Analysis of Algebraic Curves."
However, Colin Maclaurin also knew the rule earlier (1729), and it appears
in Chinese mathematics from the 12th century. Despite its elegance for
theoretical purposes, it is computationally expensive for large systems
(O(n! · n) operations), so practical implementations use Gaussian elimination.

This is #97 on Wiedijk's list of 100 theorems.
-/

namespace CramersRule

open Matrix BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

/-! ## The Cramer Map

The key construct is `Matrix.cramer`, which takes a matrix A and vector b
and produces a solution candidate vector. -/

/-- **Cramer's Rule - Component Formula (Wiedijk #97)**

The i-th component of the Cramer solution is the determinant of the matrix A
with column i replaced by the vector b.

This is the classic formula: x_i = det(A with col i ← b) -/
theorem cramer_component (A : Matrix n n R) (b : n → R) (i : n) :
    A.cramer b i = (A.updateColumn i b).det :=
  Matrix.cramer_apply A b i

/-! ## The Main Theorem: Cramer's Rule

The fundamental identity that makes Cramer's Rule work: multiplying A by
the Cramer vector gives det(A) times the original vector b. -/

/-- **Cramer's Rule - Main Identity (Wiedijk #97)**

For any matrix A and vector b:
  A * cramer(A, b) = det(A) • b

This is the core of Cramer's Rule. When det(A) is a unit (invertible),
we can divide both sides by det(A) to get the unique solution x = A⁻¹ b.

Note: This formulation works even when det(A) = 0, making it more general
than the traditional statement that requires invertibility. -/
theorem cramers_rule (A : Matrix n n R) (b : n → R) :
    A.mulVec (A.cramer b) = A.det • b :=
  Matrix.mulVec_cramer A b

/-- The solution formula when the determinant is a unit -/
theorem cramers_rule_solution (A : Matrix n n R) (b : n → R) [Invertible A.det] :
    A.mulVec (⅟A.det • A.cramer b) = b := by
  rw [mulVec_smul, cramers_rule, smul_smul, invOf_mul_self, one_smul]

/-! ## Connection to the Adjugate Matrix

Cramer's Rule is intimately connected to the adjugate (classical adjoint) matrix.
The adjugate satisfies A * adj(A) = det(A) * I. -/

/-- Cramer's solution equals the adjugate matrix times b -/
theorem cramer_eq_adjugate_mulVec (A : Matrix n n R) (b : n → R) :
    A.cramer b = A.adjugate.mulVec b :=
  Matrix.cramer_eq_adjugate_mulVec A b

/-- The adjugate-determinant identity: A * adjugate(A) = det(A) * I -/
theorem adjugate_mul_self (A : Matrix n n R) :
    A * A.adjugate = A.det • (1 : Matrix n n R) :=
  Matrix.mul_adjugate A

/-! ## Transpose Form

Cramer's Rule also has a transpose formulation for row operations. -/

/-- Cramer's Rule for the transpose: each component involves replacing a row -/
theorem cramer_transpose (A : Matrix n n R) (b : n → R) (i : n) :
    Aᵀ.cramer b i = (A.updateRow i b).det :=
  Matrix.cramer_transpose_apply A b i

/-! ## Properties of the Cramer Map

The Cramer map is linear in its second argument. -/

/-- Cramer is additive in the second argument -/
theorem cramer_add (A : Matrix n n R) (b c : n → R) :
    A.cramer (b + c) = A.cramer b + A.cramer c :=
  A.cramer.map_add b c

/-- Cramer respects scalar multiplication -/
theorem cramer_smul (A : Matrix n n R) (r : R) (b : n → R) :
    A.cramer (r • b) = r • A.cramer b :=
  A.cramer.map_smul r b

/-- Cramer of zero is zero -/
theorem cramer_zero (A : Matrix n n R) :
    A.cramer 0 = 0 :=
  A.cramer.map_zero

/-! ## Example: 2×2 System

For a 2×2 system, Cramer's Rule gives the familiar formulas:
- x = (b₁a₂₂ - b₂a₁₂) / (a₁₁a₂₂ - a₁₂a₂₁)
- y = (a₁₁b₂ - a₂₁b₁) / (a₁₁a₂₂ - a₁₂a₂₁)
-/

/-- The main identity specialized to 2×2 matrices over a field -/
example {F : Type*} [Field F] (A : Matrix (Fin 2) (Fin 2) F) (b : Fin 2 → F)
    (hdet : A.det ≠ 0) :
    A.mulVec (A.det⁻¹ • A.cramer b) = b := by
  rw [mulVec_smul, cramers_rule, smul_smul, inv_mul_cancel hdet, one_smul]

/-! ## Verification: The Core Identity -/

#check Matrix.mulVec_cramer
#check Matrix.cramer_apply
#check Matrix.cramer_eq_adjugate_mulVec
#check Matrix.mul_adjugate

end CramersRule
