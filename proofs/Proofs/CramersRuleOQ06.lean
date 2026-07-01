import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-
# The Adjugate Algebra (cramers-rule-oq-06)

The parent `cramers-rule` derives Cramer's rule from the single adjugate identity
`A * adj(A) = det(A) • I`.  This child studies the adjugate as an *operation in its own
right* and assembles its compositional algebra:

  * `adj` is an **anti-homomorphism** on products: `adj(A * B) = adj(B) * adj(A)`;
  * it commutes with **powers** and **transpose**: `adj(Aᵏ) = adj(A)ᵏ`, `adj(Aᵀ) = adj(A)ᵀ`;
  * it scales its **determinant**: `det(adj A) = (det A) ^ (n - 1)`;
  * it is an **involution up to a determinant factor**: `adj(adj A) = (det A) ^ (n - 2) • A`
    for `n ≠ 1`.

Two results are stated as *original corollaries* of the anti-homomorphism law, neither
present in Mathlib:

  * **Units have invertible adjugates that respect inversion** — if `A` and `B` are mutually
    inverse then so are `adj A` and `adj B` (`adjugate_mul_adjugate_inv`).
  * **Similar matrices have similar adjugates** — the adjugate of a conjugate is the
    conjugate of the adjugate, so `adj` descends to conjugacy classes (`adjugate_conj`).

Everything reduces to curated Mathlib lemmas chained together; the file stays
`verified`, `0` axioms, `0` sorries.
-/

namespace CramersRuleOQ06

open Matrix BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================================
-- Part I: The multiplicative / structural laws of the adjugate
-- ============================================================================

/-- The adjugate is an **anti-homomorphism** on products:
    `adj(A * B) = adj(B) * adj(A)`. -/
theorem adjugate_anti_mul (A B : Matrix n n R) :
    (A * B).adjugate = B.adjugate * A.adjugate :=
  Matrix.adjugate_mul_distrib A B

/-- The adjugate of the identity is the identity. -/
theorem adjugate_one' : (1 : Matrix n n R).adjugate = 1 :=
  Matrix.adjugate_one

/-- The adjugate commutes with **powers**: `adj(Aᵏ) = adj(A)ᵏ`. -/
theorem adjugate_pow' (A : Matrix n n R) (k : ℕ) :
    (A ^ k).adjugate = A.adjugate ^ k :=
  Matrix.adjugate_pow A k

/-- The adjugate commutes with **transpose**: `adj(Aᵀ) = adj(A)ᵀ`. -/
theorem adjugate_transpose' (A : Matrix n n R) :
    Aᵀ.adjugate = A.adjugateᵀ :=
  (Matrix.adjugate_transpose A).symm

/-- The determinant of the adjugate: `det(adj A) = (det A) ^ (n - 1)`. -/
theorem det_adjugate' (A : Matrix n n R) :
    A.adjugate.det = A.det ^ (Fintype.card n - 1) :=
  Matrix.det_adjugate A

/-- The adjugate is an **involution up to a determinant factor**:
    `adj(adj A) = (det A) ^ (n - 2) • A` when `n ≠ 1`. -/
theorem adjugate_adjugate' (A : Matrix n n R) (h : Fintype.card n ≠ 1) :
    A.adjugate.adjugate = A.det ^ (Fintype.card n - 2) • A :=
  Matrix.adjugate_adjugate A h

-- ============================================================================
-- Part II: Original corollaries of the anti-homomorphism law
-- ============================================================================

/-- **ORIGINAL.** The adjugate sends mutually-inverse pairs to mutually-inverse pairs:
    if `A * B = 1` and `B * A = 1` then `adj A` and `adj B` are mutually inverse.
    In particular the adjugate of a unit is again a unit.  Proof: apply the
    anti-homomorphism law to `B * A` and `A * B` and simplify with `adjugate_one`. -/
theorem adjugate_mul_adjugate_inv {A B : Matrix n n R} (h : A * B = 1) (h' : B * A = 1) :
    A.adjugate * B.adjugate = 1 ∧ B.adjugate * A.adjugate = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← Matrix.adjugate_mul_distrib B A, h', Matrix.adjugate_one]
  · rw [← Matrix.adjugate_mul_distrib A B, h, Matrix.adjugate_one]

/-- **ORIGINAL.** *Similar matrices have similar adjugates.*  For a conjugating pair
    `U`, `Uinv` (with `U * Uinv = 1` and `Uinv * U = 1`), the adjugate of the conjugate
    `U * A * Uinv` is the conjugate of the adjugate, `adj(Uinv) * adj(A) * adj(U)`, and the
    conjugating factors `adj U`, `adj Uinv` are themselves mutually inverse — so `adj`
    descends to conjugacy classes.  Proof: chain the anti-homomorphism law twice, then use
    `adjugate_mul_adjugate_inv`. -/
theorem adjugate_conj (A U Uinv : Matrix n n R)
    (h : U * Uinv = 1) (h' : Uinv * U = 1) :
    (U * A * Uinv).adjugate = Uinv.adjugate * A.adjugate * U.adjugate ∧
      U.adjugate * Uinv.adjugate = 1 ∧ Uinv.adjugate * U.adjugate = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, ← Matrix.mul_assoc]
  · rw [← Matrix.adjugate_mul_distrib Uinv U, h', Matrix.adjugate_one]
  · rw [← Matrix.adjugate_mul_distrib U Uinv, h, Matrix.adjugate_one]

-- ============================================================================
-- Part III: A concrete `Fin 2` witness
-- ============================================================================

/-- Concrete `Fin 2` computation: `adj !![1,2;3,4] = !![4,-2;-3,1]`. -/
example : (!![(1 : ℤ), 2; 3, 4]).adjugate = !![4, -2; -3, 1] := by
  rw [Matrix.adjugate_fin_two_of]

/-- The anti-homomorphism law, checked on a concrete `Fin 2` product. -/
example (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).adjugate = B.adjugate * A.adjugate :=
  adjugate_anti_mul A B

end CramersRuleOQ06
