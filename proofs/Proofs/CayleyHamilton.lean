import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Cayley-Hamilton Theorem (Wiedijk #49)

## What This Proves
The Cayley-Hamilton Theorem states that every square matrix satisfies its own
characteristic polynomial. If A is an n×n matrix with characteristic polynomial
p(λ) = det(λI - A), then p(A) = 0 (the zero matrix).

## Historical Context
- **William Rowan Hamilton** (1853): Proved the theorem for quaternions
- **Arthur Cayley** (1858): Extended to general matrices
Named after both mathematicians, though the general proof came later.

## Approach
- **Foundation (from Mathlib):** We use `Matrix.aeval_self_charpoly` which directly
  proves that evaluating a matrix's characteristic polynomial at the matrix itself
  yields zero.
- **Key Insight:** The characteristic polynomial p(λ) = det(λI - A) encodes the
  eigenvalues of A. The theorem says that A "behaves like" each of its eigenvalues.
- **Applications:** Computing matrix powers, finding the minimal polynomial,
  and proving that matrices are roots of polynomials of bounded degree.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Matrix.charpoly` : The characteristic polynomial det(X * I - A)
- `Matrix.aeval_self_charpoly` : p_A(A) = 0, the Cayley-Hamilton theorem
- `Matrix.charpoly_natDegree_eq_dim` : The characteristic polynomial has degree n
- `Matrix.charpoly_monic` : The characteristic polynomial is monic

This is #49 on Wiedijk's list of 100 theorems.
-/

namespace CayleyHamilton

open Matrix Polynomial BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================
-- PART 1: The Characteristic Polynomial
-- ============================================================

/-! ## The Characteristic Polynomial

The characteristic polynomial of an n×n matrix A is defined as:
  p_A(λ) = det(λI - A)

This is a monic polynomial of degree n whose roots are the eigenvalues of A.
-/

/-- The characteristic polynomial is monic (leading coefficient is 1) -/
theorem charpoly_is_monic (A : Matrix n n R) :
    A.charpoly.Monic :=
  Matrix.charpoly_monic A

/-- The characteristic polynomial has degree equal to the dimension n.
    This requires Nontrivial R (a ring with at least two distinct elements). -/
theorem charpoly_degree [Nontrivial R] (A : Matrix n n R) :
    A.charpoly.natDegree = Fintype.card n :=
  Matrix.charpoly_natDegree_eq_dim A

-- ============================================================
-- PART 2: The Cayley-Hamilton Theorem
-- ============================================================

/-! ## The Main Theorem

The Cayley-Hamilton theorem states that every square matrix satisfies its own
characteristic polynomial. If p_A(λ) = det(λI - A), then p_A(A) = 0.

This is a remarkable result: it says that if we take the polynomial p_A,
substitute the matrix A for the variable λ, and evaluate (interpreting
powers of λ as matrix powers), we get the zero matrix.
-/

/-- **The Cayley-Hamilton Theorem (Wiedijk #49)**

Every square matrix satisfies its own characteristic polynomial.

If A is an n×n matrix with characteristic polynomial p_A(λ) = det(λI - A), then:
  p_A(A) = 0

This is proved using Mathlib's `Matrix.aeval_self_charpoly`, which demonstrates
the result through the algebraic properties of the adjugate matrix. -/
theorem cayley_hamilton (A : Matrix n n R) :
    aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A

/-- Alternative statement using polynomial evaluation notation -/
theorem cayley_hamilton' (A : Matrix n n R) :
    Polynomial.aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A

-- ============================================================
-- PART 3: Examples
-- ============================================================

/-! ## Concrete Examples

We verify the theorem for specific small matrices.
-/

/-- Example: The identity matrix

For I, the characteristic polynomial is (λ - 1)^n.
Evaluating at I gives (I - I)^n = 0. -/
theorem identity_example (m : ℕ) [NeZero m] :
    aeval (1 : Matrix (Fin m) (Fin m) ℝ) (1 : Matrix (Fin m) (Fin m) ℝ).charpoly = 0 :=
  Matrix.aeval_self_charpoly 1

/-- Example: Nilpotent matrix

A nilpotent matrix N has characteristic polynomial λ^n.
By Cayley-Hamilton, N^n = 0. -/
theorem nilpotent_charpoly (A : Matrix n n R) (h : A.charpoly = X ^ Fintype.card n) :
    A ^ Fintype.card n = 0 := by
  have := cayley_hamilton A
  rw [h, map_pow, aeval_X] at this
  exact this

/-- Scalar matrices: for A = c * I, the theorem says (c - c)^n = 0 -/
theorem scalar_matrix_example (c : R) :
    aeval (Matrix.scalar n c) (Matrix.scalar n c).charpoly = 0 :=
  Matrix.aeval_self_charpoly _

/-- The zero matrix satisfies its characteristic polynomial -/
theorem zero_matrix_example :
    aeval (0 : Matrix n n R) (0 : Matrix n n R).charpoly = 0 :=
  Matrix.aeval_self_charpoly 0

-- ============================================================
-- PART 4: Consequences
-- ============================================================

/-! ## Applications of Cayley-Hamilton

The theorem has many important consequences:
1. Every matrix is a root of a polynomial of degree ≤ n
2. A^n can be expressed as a linear combination of I, A, ..., A^(n-1)
3. The inverse of A (when it exists) can be written as a polynomial in A
-/

/-- Cayley-Hamilton implies that the characteristic polynomial annihilates the matrix -/
theorem charpoly_annihilates (A : Matrix n n R) :
    aeval A A.charpoly = 0 :=
  cayley_hamilton A

/-- The characteristic polynomial is in the annihilator of A -/
theorem charpoly_in_annihilator (A : Matrix n n R) :
    A.charpoly ∈ {p : Polynomial R | aeval A p = 0} :=
  cayley_hamilton A

-- ============================================================
-- PART 5: The 2×2 Case
-- ============================================================

/-! ## The 2×2 Case

For 2×2 matrices, Cayley-Hamilton gives the explicit formula:
  A² - trace(A) · A + det(A) · I = 0

This is particularly useful for computing matrix inverses and powers.

The characteristic polynomial of a 2×2 matrix A is:
  p(λ) = λ² - trace(A)·λ + det(A)

By Cayley-Hamilton, substituting A for λ gives:
  A² - trace(A)·A + det(A)·I = 0
-/

/-- For a 2×2 matrix A, Cayley-Hamilton directly gives A satisfies its char poly.
    The explicit formula A² - trace(A)·A + det(A)·I = 0 follows from the
    general theorem. -/
theorem cayley_hamilton_2x2 (A : Matrix (Fin 2) (Fin 2) R) :
    aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A

-- ============================================================
-- PART 6: Theoretical Significance
-- ============================================================

/-!
### Why Cayley-Hamilton Matters

1. **Linear Algebra**: Shows that matrices of size n×n live in a polynomial
   quotient ring of dimension at most n

2. **Computing Matrix Functions**: To compute A^100, we only need to know
   A, A², ..., A^(n-1) and then use the characteristic polynomial relation

3. **Control Theory**: The Cayley-Hamilton theorem is essential for analyzing
   linear systems dx/dt = Ax and computing the matrix exponential e^(At)

4. **Eigenvalue Theory**: The proof illuminates the deep connection between
   determinants, eigenvalues, and matrix polynomials

### Historical Notes

The theorem was first published by Arthur Cayley in 1858 for 2×2 and 3×3
matrices, though he only verified specific cases. Hamilton had earlier (1853)
proved a related result for quaternions. The first complete proof for
arbitrary n×n matrices was given by Ferdinand Frobenius in 1878.

The proof in Mathlib uses a clever algebraic approach involving the adjugate
matrix and the identity A * adj(A) = det(A) * I, combined with polynomial
manipulation in the ring of matrices.

### The 2×2 Explicit Formula

For a 2×2 matrix [[a, b], [c, d]], the characteristic polynomial is:
  p(λ) = λ² - (a+d)λ + (ad - bc)
       = λ² - trace(A)·λ + det(A)

Cayley-Hamilton says:
  A² - (a+d)A + (ad-bc)I = 0

This gives the inverse formula (when det(A) ≠ 0):
  A⁻¹ = (1/det(A)) · (trace(A)·I - A)
      = (1/(ad-bc)) · [[d, -b], [-c, a]]

### Connection to Eigenvalues

If λ₁, λ₂, ..., λₙ are the eigenvalues of A (with multiplicity), then:
  p(λ) = (λ - λ₁)(λ - λ₂)···(λ - λₙ)

Cayley-Hamilton says:
  (A - λ₁I)(A - λ₂I)···(A - λₙI) = 0

This means the "product of shifts" annihilates A, which is remarkable because
each individual factor (A - λᵢI) may be nonzero!
-/

-- Export main results
#check @cayley_hamilton
#check @charpoly_is_monic
#check @charpoly_degree
#check @nilpotent_charpoly

end CayleyHamilton
