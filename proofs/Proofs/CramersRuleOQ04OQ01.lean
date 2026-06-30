import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Cramer's rule OQ-04 → OQ-01: the adjugate behind Cayley–Hamilton

The parent chain (`cramers-rule`) develops Cramer's rule via the adjugate matrix. Its
OQ-04-OQ-01 asks to

> *formalize the algebraic Cayley–Hamilton proof via* `adj(xI − A)·(xI − A) = χ_A(x)·I`,
> *the adjugate reflexive property.*

Both Cramer's rule and the Cayley–Hamilton theorem rest on the **same** adjugate identity
`adjugate B · B = (det B)·I`. Cramer's rule applies it to a scalar matrix `B = A`; Cayley–
Hamilton applies it to the **characteristic matrix** `B = xI − A` over the polynomial ring
`R[X]`, where `det(xI − A) = χ_A(x)`, giving `adj(xI − A)·(xI − A) = χ_A(x)·I`, and then
evaluates at `A`. Mathlib proves Cayley–Hamilton this way (`Matrix.aeval_self_charpoly`); we
package the underlying adjugate identities in gallery form and tie the two theorems to their
common source. `0` axioms.

## Main results

* `adjugate_charmatrix_mul` : `adj(xI − A)·(xI − A) = χ_A(x)·I` (the reflexive identity).
* `cayley_hamilton` : `χ_A(A) = 0`.
* `minpoly_dvd_charpoly` : the minimal polynomial divides the characteristic polynomial.
* `adjugate_mulVec_solve` : `A·(adj A · b) = (det A)·b` — the adjugate solves `Ax = b` up to
  the determinant, the determinant form of Cramer's rule.
-/

namespace CramersRuleOQ04OQ01

open Matrix Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **The adjugate-reflexive identity.** Over the polynomial ring `R[X]`, the adjugate of the
    characteristic matrix `xI − A` times the characteristic matrix is the characteristic
    polynomial times the identity:  `adj(xI − A)·(xI − A) = χ_A(x)·I`. This is the algebraic
    heart of the Cayley–Hamilton theorem. -/
theorem adjugate_charmatrix_mul (M : Matrix n n R) :
    adjugate (charmatrix M) * charmatrix M = M.charpoly • 1 :=
  adjugate_mul (charmatrix M)

/-- **Cayley–Hamilton.** A matrix satisfies its own characteristic polynomial: `χ_A(A) = 0`.
    Obtained from the adjugate-reflexive identity by passing to `Polynomial (Matrix n n R)`
    and evaluating at `A` (Mathlib: `Matrix.aeval_self_charpoly`). -/
theorem cayley_hamilton (M : Matrix n n R) : aeval M M.charpoly = 0 :=
  aeval_self_charpoly M

/-- **Minimal divides characteristic.** Over a field, the minimal polynomial of `A` divides
    its characteristic polynomial — a direct consequence of Cayley–Hamilton. -/
theorem minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) :
    minpoly K M ∣ M.charpoly :=
  Matrix.minpoly_dvd_charpoly M

/-- **The other adjugate identity** `A·adj(A) = (det A)·I`, the source of Cramer's rule. -/
theorem mul_adjugate_eq (A : Matrix n n R) :
    A * adjugate A = A.det • 1 :=
  mul_adjugate A

/-- **Determinant form of Cramer's rule.** The adjugate solves the linear system `A x = b`
    up to the determinant: `A·(adj A · b) = (det A)·b`. When `det A` is a unit this gives the
    explicit solution `x = (det A)⁻¹ · adj A · b` — Cramer's rule. The same adjugate identity
    `A·adj A = (det A)·I` underlies both this and the Cayley–Hamilton identity above. -/
theorem adjugate_mulVec_solve (A : Matrix n n R) (b : n → R) :
    A *ᵥ (adjugate A *ᵥ b) = A.det • b := by
  rw [mulVec_mulVec, mul_adjugate, smul_mulVec_assoc, one_mulVec]

end CramersRuleOQ04OQ01
