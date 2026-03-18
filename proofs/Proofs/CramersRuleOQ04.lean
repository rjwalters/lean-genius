import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-
# Cramer's Rule and Generalized Inverses (cramers-rule-oq-04)

The adjugate matrix adj(A) provides a "generalized inverse" that extends
Cramer's rule to singular matrices.

Key identities:
  A * adj(A) = det(A) * I     (always holds)
  adj(A) * A = det(A) * I     (always holds)

When det(A) is invertible: A⁻¹ = adj(A) / det(A)
When det(A) = 0: adj(A) still satisfies generalized inverse properties

This file formalizes:
1. The adjugate as a generalized inverse (1-reflexive property)
2. The non-singular case: adjugate recovers the inverse
3. Cramer's formula in terms of adjugate (for all matrices)
4. The singular case: what adj(A) * b computes

Status: 0 axioms, 0 sorries
-/

namespace CramersRuleOQ04

open Matrix BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================================
-- Part I: Adjugate Identities (Generalized Inverse Properties)
-- ============================================================================

/-- The adjugate satisfies A * adj(A) = det(A) * I. -/
theorem adjugate_right (A : Matrix n n R) :
    A * A.adjugate = A.det • (1 : Matrix n n R) :=
  Matrix.mul_adjugate A

/-- The adjugate satisfies adj(A) * A = det(A) * I. -/
theorem adjugate_left (A : Matrix n n R) :
    A.adjugate * A = A.det • (1 : Matrix n n R) :=
  Matrix.adjugate_mul A

/-- **1-Reflexive Property**: A * adj(A) * A = det(A) * A.
    This is the key generalized inverse identity. For true generalized
    inverses (Moore-Penrose), we'd need A * G * A = A, but the adjugate
    satisfies A * adj(A) * A = det(A) * A, which reduces to A * G * A = A
    when we set G = adj(A)/det(A) for invertible det(A). -/
theorem adjugate_reflexive (A : Matrix n n R) :
    A * A.adjugate * A = A.det • A := by
  rw [Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]

/-- Symmetric 1-reflexive property: adj(A) * A * adj(A) = det(A) * adj(A). -/
theorem adjugate_reflexive_sym (A : Matrix n n R) :
    A.adjugate * A * A.adjugate = A.det • A.adjugate := by
  rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

-- ============================================================================
-- Part II: Non-Singular Case (Adjugate = det * Inverse)
-- ============================================================================

/-- When det(A) is invertible, scaling the adjugate by det(A)⁻¹ gives an inverse.
    Proof: A * (⅟det(A) • adj(A)) = ⅟det(A) • (A * adj(A)) = ⅟det(A) • det(A) • I = I. -/
theorem adjugate_scaled_is_right_inv (A : Matrix n n R) [Invertible A.det] :
    A * (⅟A.det • A.adjugate) = 1 := by
  rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, invOf_mul_self, one_smul]

/-- Cramer's solution via adjugate gives the actual solution when A is invertible. -/
theorem cramer_adjugate_solution (A : Matrix n n R) (b : n → R) [Invertible A.det] :
    A.mulVec (⅟A.det • A.adjugate.mulVec b) = b := by
  rw [mulVec_smul, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_cramer,
      smul_smul, invOf_mul_self, one_smul]

-- ============================================================================
-- Part III: Cramer's Formula via Adjugate (General Case)
-- ============================================================================

/-- The generalized Cramer formula: A * adj(A) * b = det(A) * b.
    This holds for ALL matrices, not just invertible ones. -/
theorem cramer_generalized (A : Matrix n n R) (b : n → R) :
    A.mulVec (A.adjugate.mulVec b) = A.det • b := by
  rw [← Matrix.cramer_eq_adjugate_mulVec]
  exact Matrix.mulVec_cramer A b

/-- Adjugate applied to b always solves the "scaled system" A * x = det(A) * b.
    When det(A) ≠ 0, dividing by det(A) gives the actual solution.
    When det(A) = 0, this says A * adj(A) * b = 0, which is consistent but trivial. -/
theorem adjugate_solves_scaled_system (A : Matrix n n R) (b : n → R) :
    A.mulVec (A.adjugate.mulVec b) = A.det • b :=
  cramer_generalized A b

-- ============================================================================
-- Part IV: Singular Case Analysis
-- ============================================================================

/-- When det(A) = 0, the adjugate maps everything to the kernel of A:
    A * adj(A) * b = 0 for all b. -/
theorem adjugate_kernel_singular (A : Matrix n n R) (b : n → R)
    (h : A.det = 0) :
    A.mulVec (A.adjugate.mulVec b) = 0 := by
  rw [cramer_generalized, h, zero_smul]

/-- When det(A) = 0, each column of adj(A) is in ker(A).
    This follows from A * adj(A) = det(A) * I = 0. -/
theorem adjugate_cols_in_kernel (A : Matrix n n R) (j : n)
    (h : A.det = 0) :
    A.mulVec (fun i => A.adjugate i j) = 0 := by
  ext i
  simp only [Matrix.mulVec, Pi.zero_apply]
  have hmul := congr_fun (congr_fun (Matrix.mul_adjugate A) i) j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, h,
             zero_mul, ite_mul, one_mul] at hmul
  exact hmul

-- ============================================================================
-- Part V: Determinant of Adjugate
-- ============================================================================

/-- The determinant of the adjugate: det(adj(A)) = det(A)^(n-1).
    This connects the adjugate to the spectral theory of A. -/
theorem det_adjugate (A : Matrix n n R) :
    A.adjugate.det = A.det ^ (Fintype.card n - 1) :=
  Matrix.det_adjugate A

-- ============================================================================
-- Part VI: Adjugate of Adjugate (Iteration)
-- ============================================================================

-- For invertible A: adj(adj(A)) = det(A)^(n-2) * A.
-- This shows the adjugate is essentially an involution (up to scalar).
-- Omitted: Mathlib's Matrix.adjugate_adjugate API requires specific IsUnit handling.

-- ============================================================================
-- Part VII: Summary
-- ============================================================================

/-
## Summary of Generalized Inverse Properties

The adjugate matrix adj(A) serves as a "generalized inverse" for Cramer's rule:

| Property | Formula | Status |
|----------|---------|--------|
| Right identity | A * adj(A) = det(A) * I | proved |
| Left identity | adj(A) * A = det(A) * I | proved |
| 1-reflexive | A * adj(A) * A = det(A) * A | proved |
| Symmetric reflexive | adj(A) * A * adj(A) = det(A) * adj(A) | proved |
| Non-singular inverse | A⁻¹ = det(A)⁻¹ * adj(A) | proved |
| Generalized Cramer | A * adj(A) * b = det(A) * b | proved |
| Singular kernel | A * adj(A) * b = 0 when det(A) = 0 | proved |
| Adjugate columns | adj(A) cols ∈ ker(A) when singular | proved |
| det(adj(A)) | = det(A)^(n-1) | proved |

The adjugate is not a Moore-Penrose pseudoinverse (which satisfies AGA = A),
but it satisfies AGA = det(A)·A, which reduces to the Moore-Penrose property
AGA = A when det(A) = 1 (unimodular matrices).

### Connection to Cramer's Rule
Cramer's classical formula x_i = det(A_i)/det(A) is equivalent to
x = adj(A)·b / det(A), which is the adjugate applied to b, scaled by 1/det(A).
The adjugate formulation works for all matrices (giving adj(A)·b = det(A)·x),
while the classical formula requires det(A) ≠ 0.
-/

end CramersRuleOQ04

#check CramersRuleOQ04.adjugate_reflexive
#check CramersRuleOQ04.cramer_generalized
#check CramersRuleOQ04.adjugate_scaled_is_right_inv
#check CramersRuleOQ04.adjugate_kernel_singular
#check CramersRuleOQ04.det_adjugate
