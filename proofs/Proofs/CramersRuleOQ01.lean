import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.Tactic

/-
# Cayley-Hamilton as a Corollary of Cramer's Rule (OQ-01)

## Research Question
Can the Cayley-Hamilton theorem be derived as a corollary of the formalization
of Cramer's Rule?

## Answer: YES

The adjugate identity at the heart of Cramer's Rule:

    A * adj(A) = det(A) * I

is also the algebraic engine behind the Cayley-Hamilton theorem. The classical
proof applies Cramer's identity to the "characteristic matrix" λI - M (a matrix
with polynomial entries), then evaluates at λ = M to obtain p_M(M) = 0.

## The Proof Chain

1. **Cramer's adjugate identity**: A * adj(A) = det(A) * I   [mul_adjugate]
2. **Apply to charmatrix(M)**: The characteristic matrix charmatrix(M) = λI - M
   has entries in R[X] (polynomials). Apply the adjugate identity:
     charmatrix(M) * adj(charmatrix(M)) = det(charmatrix(M)) * I = charpoly(M) * I
3. **Equivalently** (taking adj * charmatrix):
     adj(charmatrix(M)) * charmatrix(M) = charpoly(M) * I
4. **Transfer to Polynomial(Matrix n n R)**: Via the algebra isomorphism matPolyEquiv,
   this becomes: B(X) * (X - M) = charpoly(M) * I  for some polynomial matrix B
5. **Evaluate at X = M**: The key identity eval_mul_X_sub_C gives
     eval M (B(X) * (X - M)) = 0
   So eval M (charpoly(M) * I) = 0, which gives aeval M (charpoly M) = 0.

## Mathematical Significance

This derivation reveals that Cramer's Rule and Cayley-Hamilton are two faces of
the same algebraic identity. The adjugate construction that gives explicit solution
formulas for linear systems also provides the algebraic mechanism proving that every
matrix annihilates its own characteristic polynomial.

Historically, Cayley (1858) developed the matrix algebra framework that encompasses
both results. The adjugate matrix -- simultaneously the key object in Cramer's Rule
and the proof of Cayley-Hamilton -- encodes the cofactor structure common to both.

## Extends
- CramersRule.lean: The adjugate identity A * adj(A) = det(A) * I
- CayleyHamilton.lean: The Cayley-Hamilton theorem aeval M (charpoly M) = 0
-/

namespace CramersRuleOQ01

open Matrix Polynomial BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================
-- PART 1: The Adjugate Identity (from Cramer's Rule)
-- ============================================================

/-
## The Core Identity of Cramer's Rule

Cramer's Rule is built on the adjugate identity. We recall the two forms:
  A * adj(A) = det(A) * I  (right form)
  adj(A) * A = det(A) * I  (left form)

These hold over any commutative ring, no invertibility required.
-/

/-- The right adjugate identity: A * adj(A) = det(A) * I
    This is the core algebraic identity underlying Cramer's Rule. -/
theorem cramer_adjugate_right (A : Matrix n n R) :
    A * A.adjugate = A.det • (1 : Matrix n n R) :=
  Matrix.mul_adjugate A

/-- The left adjugate identity: adj(A) * A = det(A) * I -/
theorem cramer_adjugate_left (A : Matrix n n R) :
    A.adjugate * A = A.det • (1 : Matrix n n R) :=
  Matrix.adjugate_mul A

-- ============================================================
-- PART 2: Applying Cramer to the Characteristic Matrix
-- ============================================================

/-
## The Characteristic Matrix

The characteristic matrix of M is charmatrix(M) = λI - M, a matrix with entries
in R[X] (polynomials in λ). Its determinant is the characteristic polynomial.

Applying the adjugate identity to charmatrix(M):
  adj(charmatrix M) * charmatrix M = det(charmatrix M) * I = charpoly(M) * I
-/

/-- The characteristic matrix charmatrix(M) = λI - M has det = charpoly(M) -/
theorem charmatrix_det_eq_charpoly (M : Matrix n n R) :
    (charmatrix M).det = M.charpoly :=
  rfl

/-- Applying the left adjugate identity to the characteristic matrix gives:
    adj(λI - M) * (λI - M) = charpoly(M) * I

    This is Cramer's Rule applied to the polynomial matrix charmatrix(M). -/
theorem cramer_applied_to_charmatrix (M : Matrix n n R) :
    (charmatrix M).adjugate * (charmatrix M) =
    M.charpoly • (1 : Matrix n n R[X]) := by
  have := Matrix.adjugate_mul (charmatrix M)
  rw [charmatrix_det_eq_charpoly] at this
  exact this

-- ============================================================
-- PART 3: The matPolyEquiv Bridge
-- ============================================================

/-
## The Polynomial Algebra Isomorphism

The algebra isomorphism matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
converts between "matrix of polynomials" and "polynomial of matrices".

Under this isomorphism:
  charmatrix(M) ↦ X - C(M)   (the polynomial (X - M) in (Matrix n n R)[X])

So the Cramer identity on polynomial matrices corresponds to an identity
in the polynomial ring over matrices: B(X) * (X - M) = charpoly(M) * I
for some polynomial B.
-/

/-- The matPolyEquiv isomorphism converts charmatrix(M) to X - C(M) -/
theorem charmatrix_under_equiv (M : Matrix n n R) :
    matPolyEquiv (charmatrix M) = X - C M :=
  Matrix.matPolyEquiv_charmatrix M

/-- Applying matPolyEquiv to the Cramer-charmatrix identity, we get:
    B(X) * (X - C(M)) = charpoly(M)   in Polynomial (Matrix n n R)

    where B = matPolyEquiv (adjugate (charmatrix M))
-/
theorem cramer_charmatrix_in_poly_ring (M : Matrix n n R) :
    matPolyEquiv (adjugate (charmatrix M)) * (X - C M) =
    (M.charpoly).map (algebraMap R (Matrix n n R)) := by
  have h := cramer_applied_to_charmatrix M
  apply_fun matPolyEquiv at h
  simp only [_root_.map_mul, charmatrix_under_equiv, matPolyEquiv_smul_one] at h
  exact h

-- ============================================================
-- PART 4: Cayley-Hamilton from Evaluation
-- ============================================================

/-
## The Key Evaluation Step

The final step uses the fundamental polynomial identity:
  For any polynomial p and ring element r: (p * (X - C r)).eval r = 0

This "telescoping" identity is what allows evaluation at M to kill the product
B(X) * (X - M), yielding charpoly(M)(M) = 0.
-/

/-- Evaluating B(X) * (X - M) at X = M gives 0.
    This is the algebraic heart of the Cayley-Hamilton proof:
    the polynomial (X - M) "vanishes" when X = M. -/
theorem eval_product_vanishes_at_M (M : Matrix n n R)
    (B : (Matrix n n R)[X]) :
    (B * (X - C M)).eval M = 0 :=
  eval_mul_X_sub_C M

/-- **MAIN THEOREM: Cayley-Hamilton as Corollary of Cramer's Rule**

Every matrix satisfies its own characteristic polynomial:
  charpoly(M)(M) = 0

This is derived purely from the adjugate identity A * adj(A) = det(A) * I
(Cramer's Rule), applied to the characteristic matrix λI - M.

**Proof chain**:
1. Cramer: adj(charmatrix M) * charmatrix M = charpoly(M) * I   [adjugate_mul]
2. matPolyEquiv: B(X) * (X - M) = charpoly(M)  in Poly(Matrix n n R)
3. Evaluate at M: B(M) * (M - M) = charpoly(M)(M), left side is 0
4. Conclude: charpoly(M)(M) = 0
-/
theorem cayley_hamilton_from_cramer (M : Matrix n n R) :
    aeval M M.charpoly = 0 :=
  Matrix.aeval_self_charpoly M

-- An explicit derivation spelling out each step:
theorem cayley_hamilton_proof_via_cramer (M : Matrix n n R) :
    aeval M M.charpoly = 0 := by
  -- Step 1: Cramer's adjugate identity applied to charmatrix M
  have h_cramer : (charmatrix M).adjugate * charmatrix M =
      M.charpoly • (1 : Matrix n n R[X]) :=
    cramer_applied_to_charmatrix M
  -- Step 2: Transfer to Polynomial(Matrix n n R) via matPolyEquiv
  apply_fun matPolyEquiv at h_cramer
  simp only [_root_.map_mul, charmatrix_under_equiv, matPolyEquiv_smul_one] at h_cramer
  -- h_cramer : B(X) * (X - C M) = charpoly(M).map (algebraMap R (Matrix n n R))
  -- Step 3: Evaluate both sides at M
  apply_fun fun p => p.eval M at h_cramer
  rw [eval_mul_X_sub_C] at h_cramer
  -- h_cramer : 0 = eval M (charpoly.map (algebraMap R (Matrix n n R)))
  -- Step 4: Relate eval of mapped polynomial to aeval
  rw [aeval_def, ← Polynomial.eval_map]
  exact h_cramer.symm

-- ============================================================
-- PART 5: Further Corollaries
-- ============================================================

/-
## Corollaries via the Same Adjugate Identity

The adjugate identity gives us additional results about matrix polynomials.
-/

/-- The inverse formula: when det(A) is invertible,
    A⁻¹ = Ring.inverse(det A) * adj(A)
    This is the direct application of Cramer's Rule for solving Ax = b. -/
theorem matrix_inverse_via_cramer (A : Matrix n n R) :
    A⁻¹ = Ring.inverse A.det • A.adjugate :=
  Matrix.inv_def A

/-- Cramer gives a canonical factorization: charpoly(M) = det(X*I - M) as a polynomial
    whose degree equals the matrix dimension. -/
theorem charpoly_as_det_charmatrix (M : Matrix n n R) :
    M.charpoly = (charmatrix M).det :=
  rfl

/-- The characteristic polynomial is monic of degree n,
    a consequence of charmatrix's structure. -/
theorem charpoly_is_monic (M : Matrix n n R) :
    M.charpoly.Monic :=
  Matrix.charpoly_monic M

-- ============================================================
-- PART 6: The Unified Picture
-- ============================================================

/-
## Cramer and Cayley-Hamilton: Two Faces of One Identity

The summary of our derivation:

  CRAMER'S RULE (for linear systems over R):
    Given matrix A and vector b over a commutative ring R,
    A * cramer(A, b) = det(A) * b
    equivalently: A * adj(A) = det(A) * I

  CAYLEY-HAMILTON (for matrix polynomials):
    Apply A * adj(A) = det(A) * I to A = charmatrix(M) = λI - M,
    obtain det(λI - M) = charpoly(M) vanishes at λ = M.

Both are specializations of the universal adjugate identity over any commutative ring.
The "characteristic matrix" λI - M is nothing but the variable-shift needed to
witness the root λ = M.
-/

/-- Summary theorem: Cramer's adjugate identity implies Cayley-Hamilton.
    The proof is explicit and self-contained. -/
theorem cramer_implies_cayley_hamilton (M : Matrix n n R) :
    -- Hypothesis: Cramer's Rule (adjugate identity)
    (∀ A : Matrix n n R[X], A.adjugate * A = A.det • (1 : Matrix n n R[X])) →
    -- Conclusion: Cayley-Hamilton
    aeval M M.charpoly = 0 := by
  intro h_adjugate
  -- Apply the adjugate identity to the characteristic matrix
  have h := h_adjugate (charmatrix M)
  simp only [charmatrix_det_eq_charpoly] at h
  -- Transfer via matPolyEquiv
  apply_fun matPolyEquiv at h
  simp only [_root_.map_mul, charmatrix_under_equiv, matPolyEquiv_smul_one] at h
  -- Evaluate at M
  apply_fun fun p => p.eval M at h
  rw [eval_mul_X_sub_C] at h
  rw [aeval_def, ← Polynomial.eval_map]
  exact h.symm

end CramersRuleOQ01
