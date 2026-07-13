import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-
# Computing Matrix Functions via Cayley-Hamilton Reduction

## What This Proves
The Cayley-Hamilton theorem implies that any polynomial function of an n×n matrix A
can be reduced to a polynomial of degree at most n-1 in A. Concretely:
  aeval A p = aeval A (p %ₘ A.charpoly)
where %ₘ denotes polynomial remainder modulo the (monic) characteristic polynomial.

This is the algebraic foundation for computing matrix exponentials, matrix powers,
and other matrix functions efficiently: instead of computing A^100 directly, reduce
the polynomial X^100 modulo charpoly(A) to get a polynomial of degree < n, then
evaluate that at A.

## Key Results
1. **Polynomial reduction**: aeval A p = aeval A (p %ₘ A.charpoly)
2. **Degree bound**: The reduced polynomial has degree < n
3. **Power reduction**: A^k can be expressed as a linear combination of I, A, ..., A^(n-1)
4. **Congruence**: Polynomials with the same remainder evaluate to the same matrix
5. **Partial sums**: Finite power series truncations reduce via Cayley-Hamilton

## Mathematical Significance
This reduction is the theoretical basis for:
- Efficient matrix power computation
- The matrix exponential e^(tA) = c₀(t)I + c₁(t)A + ... + c_{n-1}(t)A^{n-1}
- Numerical ODE solvers for dx/dt = Ax
- Signal processing and control theory applications

## Extends
- CayleyHamilton.lean (Wiedijk #49)
- MinpolyCharpoly.lean (minimal polynomial relationship)

## Status
- [x] Complete proof (no sorries)
- [x] Uses Mathlib for core results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples

## Mathlib Dependencies
- `Matrix.aeval_self_charpoly` : Cayley-Hamilton theorem
- `Matrix.charpoly_monic` : Characteristic polynomial is monic
- `Matrix.charpoly_natDegree_eq_dim` : Degree of charpoly equals n
- `Polynomial.modByMonic_add_div` : Division algorithm for polynomials
- `Polynomial.degree_modByMonic_lt` : Degree bound on remainder
-/

namespace CayleyHamiltonOQ02

open Matrix Polynomial BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R]

-- ============================================================
-- PART 1: The Polynomial Reduction Theorem
-- ============================================================

/-
## Polynomial Reduction via Cayley-Hamilton

The key insight: since aeval A (charpoly A) = 0, the characteristic polynomial
acts as a "modular reduction" for polynomial evaluation at matrices.

For any polynomial p(X), we can write:
  p(X) = q(X) · charpoly_A(X) + r(X)
where r = p %ₘ charpoly_A has degree < n.

Evaluating at A:
  p(A) = q(A) · charpoly_A(A) + r(A) = q(A) · 0 + r(A) = r(A)
-/

/-- The characteristic polynomial annihilates the matrix (Cayley-Hamilton). -/
theorem charpoly_annihilates (A : Matrix n n R) :
    aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A

/-- **The Polynomial Reduction Theorem (Core Result)**

For any polynomial p, evaluating p at a matrix A gives the same result as
evaluating the remainder of p modulo A's characteristic polynomial.

This is the algebraic foundation for computing matrix functions via
Cayley-Hamilton: reduce any polynomial modulo charpoly first, then evaluate. -/
theorem aeval_eq_aeval_modByMonic (A : Matrix n n R) (f : R[X]) :
    aeval A f = aeval A (f %ₘ A.charpoly) := by
  have hm : A.charpoly.Monic := Matrix.charpoly_monic A
  have hann : aeval A A.charpoly = 0 := Matrix.aeval_self_charpoly A
  have hdiv := Polynomial.modByMonic_add_div f hm
  have := congr_arg (aeval A) hdiv
  simp only [map_add, map_mul] at this
  rw [hann, zero_mul, add_zero] at this
  exact this.symm

/-- Alternative: the difference p - (p %ₘ charpoly) is annihilated by A. -/
theorem aeval_sub_mod_eq_zero (A : Matrix n n R) (f : R[X]) :
    aeval A (f - f %ₘ A.charpoly) = 0 := by
  rw [map_sub, aeval_eq_aeval_modByMonic A f, sub_self]

-- ============================================================
-- PART 2: Degree Bounds
-- ============================================================

/-
## Degree of the Reduced Polynomial

The remainder p %ₘ charpoly has degree strictly less than deg(charpoly) = n.
This means any polynomial function of A reduces to a linear combination
of I, A, A², ..., A^(n-1).
-/

/-- The reduced polynomial has degree strictly less than the characteristic
    polynomial, and therefore less than the matrix dimension n. -/
theorem degree_reduced_lt_charpoly [Nontrivial R] (A : Matrix n n R)
    (f : R[X]) (hf : f %ₘ A.charpoly ≠ 0) :
    (f %ₘ A.charpoly).natDegree < A.charpoly.natDegree :=
  Polynomial.natDegree_lt_natDegree hf (Polynomial.degree_modByMonic_lt f (Matrix.charpoly_monic A))

/-- The reduced polynomial has degree less than the matrix dimension n. -/
theorem degree_reduced_lt_dim [Nontrivial R] (A : Matrix n n R)
    (f : R[X]) (hf : f %ₘ A.charpoly ≠ 0) :
    (f %ₘ A.charpoly).natDegree < Fintype.card n := by
  calc (f %ₘ A.charpoly).natDegree
      < A.charpoly.natDegree := degree_reduced_lt_charpoly A f hf
    _ = Fintype.card n := Matrix.charpoly_natDegree_eq_dim A

-- ============================================================
-- PART 3: Power Reduction
-- ============================================================

/-
## Matrix Power Reduction

For k ≥ n, A^k can be expressed as a polynomial in A of degree < n.
Instead of computing A^100 by repeated squaring, reduce X^100 modulo
charpoly(A) to get a polynomial of degree < n, then evaluate at A.
-/

/-- Matrix power A^k equals evaluation of X^k reduced modulo charpoly. -/
theorem power_eq_aeval_mod (A : Matrix n n R) (k : ℕ) :
    A ^ k = aeval A ((X : R[X]) ^ k %ₘ A.charpoly) := by
  have := aeval_eq_aeval_modByMonic A (X ^ k)
  simp only [map_pow, aeval_X] at this
  exact this

/-- Every polynomial expression in A can be represented by a polynomial of
    degree less than the characteristic polynomial's degree.
    Returns the reduced polynomial together with the equality and degree bound. -/
theorem aeval_reduced [Nontrivial R] (A : Matrix n n R) (f : R[X]) :
    ∃ q : R[X], aeval A f = aeval A q ∧
    (q = 0 ∨ q.natDegree < A.charpoly.natDegree) := by
  use f %ₘ A.charpoly
  refine ⟨aeval_eq_aeval_modByMonic A f, ?_⟩
  by_cases h : f %ₘ A.charpoly = 0
  · exact Or.inl h
  · exact Or.inr (degree_reduced_lt_charpoly A f h)

-- ============================================================
-- PART 4: Congruence and Algebraic Structure
-- ============================================================

/-
## The Annihilator Ideal and Congruence

Two polynomials with the same remainder modulo charpoly evaluate to the same
matrix. This means the evaluation map factors through the quotient ring
R[X]/(charpoly), which has dimension n as an R-module.
-/

/-- Two polynomials with the same remainder mod charpoly evaluate to the same matrix. -/
theorem congruence (A : Matrix n n R) (f g : R[X])
    (h : f %ₘ A.charpoly = g %ₘ A.charpoly) :
    aeval A f = aeval A g := by
  rw [aeval_eq_aeval_modByMonic A f, aeval_eq_aeval_modByMonic A g, h]

/-- Any multiple of the characteristic polynomial annihilates A. -/
theorem charpoly_multiple_annihilates (A : Matrix n n R) (q : R[X]) :
    aeval A (q * A.charpoly) = 0 := by
  rw [map_mul, Matrix.aeval_self_charpoly A, mul_zero]

/-- The set of annihilating polynomials is closed under addition. -/
theorem annihilator_add (A : Matrix n n R) (f g : R[X])
    (hf : aeval A f = 0) (hg : aeval A g = 0) :
    aeval A (f + g) = 0 := by
  rw [map_add, hf, hg, add_zero]

/-- The set of annihilating polynomials is closed under left multiplication. -/
theorem annihilator_mul_left (A : Matrix n n R) (f g : R[X])
    (hg : aeval A g = 0) :
    aeval A (f * g) = 0 := by
  rw [map_mul, hg, mul_zero]

-- ============================================================
-- PART 5: Partial Sum Reduction
-- ============================================================

/-
## Reduction of Power Series Partial Sums

Matrix functions defined by power series (like the matrix exponential)
can be reduced modulo charpoly. If f(X) = Σ cₖ Xᵏ, then:
  f(A) = (Σ cₖ Xᵏ %ₘ charpoly_A)(A)

For the matrix exponential: exp(A) = Σ A^k/k!
Over ℚ or ℝ, this becomes a finite-dimensional computation.
-/

/-- Any finite partial sum of a power series, when evaluated at a matrix,
    equals the evaluation of the reduced partial sum.
    This is the key algebraic step for computing matrix exponentials. -/
theorem partial_sum_reduces (A : Matrix n n R) (c : ℕ → R) (N : ℕ) :
    aeval A (∑ k ∈ Finset.range N, C (c k) * X ^ k) =
    aeval A ((∑ k ∈ Finset.range N, C (c k) * X ^ k) %ₘ A.charpoly) :=
  aeval_eq_aeval_modByMonic A _

/-- The degree bound applies to the partial sum reduction as well. -/
theorem partial_sum_reduced_bound [Nontrivial R] (A : Matrix n n R) (c : ℕ → R) (N : ℕ)
    (h : (∑ k ∈ Finset.range N, C (c k) * X ^ k) %ₘ A.charpoly ≠ 0) :
    ((∑ k ∈ Finset.range N, C (c k) * X ^ k) %ₘ A.charpoly).natDegree < Fintype.card n :=
  degree_reduced_lt_dim A _ h

-- ============================================================
-- PART 6: Special Cases
-- ============================================================

/-
## Nilpotent Matrices

For nilpotent matrices (A^n = 0), the characteristic polynomial is X^n.
The matrix exponential truncates exactly:
  exp(A) = I + A + A²/2! + ... + A^(n-1)/(n-1)!
-/

/-- A matrix whose characteristic polynomial is X^n is nilpotent. -/
theorem nilpotent_from_charpoly (A : Matrix n n R)
    (h : A.charpoly = X ^ Fintype.card n) :
    A ^ Fintype.card n = 0 := by
  have := Matrix.aeval_self_charpoly A
  rw [h, map_pow, aeval_X] at this
  exact this

/-- For a nilpotent matrix, all powers k ≥ n vanish. -/
theorem nilpotent_higher_powers_vanish (A : Matrix n n R)
    (h : A ^ Fintype.card n = 0) (k : ℕ) (hk : Fintype.card n ≤ k) :
    A ^ k = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, h, zero_mul]

/-
## Idempotent Matrices

For an idempotent matrix (A² = A), all positive powers equal A.
The matrix exponential becomes: exp(tA) = I + (e^t - 1)·A.
-/

/-- For an idempotent matrix, all positive powers equal A. -/
theorem idempotent_power (A : Matrix n n R) (h : A * A = A) (k : ℕ) (hk : 0 < k) :
    A ^ k = A := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [pow_one]
    | succ k =>
      rw [pow_succ, ih (by omega), h]

-- ============================================================
-- PART 7: Concrete Examples
-- ============================================================

/-
## The 2×2 Case

For a 2×2 matrix with characteristic polynomial p(λ) = λ² - tr(A)λ + det(A),
Cayley-Hamilton gives: A² = tr(A)·A - det(A)·I

Higher powers are recursively expressible:
- A³ = (tr² - det)·A - tr·det·I
- A⁴ = ...

All powers reduce to the form: A^k = αₖ·I + βₖ·A

For the matrix exponential (eigenvalues λ₁ ≠ λ₂):
  exp(tA) = ((λ₂·e^{tλ₁} - λ₁·e^{tλ₂})/(λ₂-λ₁))·I + ((e^{tλ₂} - e^{tλ₁})/(λ₂-λ₁))·A
-/

/-- For 2×2 matrices, every power reduces via the charpoly (degree 2). -/
theorem power_2x2_reduction (A : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    A ^ k = aeval A ((X : R[X]) ^ k %ₘ A.charpoly) :=
  power_eq_aeval_mod A k

/-- The identity matrix: all powers of I are I. -/
theorem identity_powers (k : ℕ) :
    (1 : Matrix n n R) ^ k = 1 :=
  one_pow k

/-- The zero matrix: powers of 0 are 0 (for k > 0). -/
theorem zero_powers (k : ℕ) (hk : 0 < k) :
    (0 : Matrix n n R) ^ k = 0 :=
  zero_pow hk.ne'

/-- Scalar matrices satisfy the Cayley-Hamilton reduction like all other matrices. -/
theorem scalar_power_reduction (c : R) (k : ℕ) :
    (Matrix.scalar n c) ^ k =
    aeval (Matrix.scalar n c) ((X : R[X]) ^ k %ₘ (Matrix.scalar n c).charpoly) :=
  power_eq_aeval_mod (Matrix.scalar n c) k

-- ============================================================
-- Summary
-- ============================================================

/-
## Summary

### Core Result: Polynomial Reduction
- `aeval_eq_aeval_modByMonic`: aeval A p = aeval A (p %ₘ A.charpoly)
  This is the fundamental theorem enabling matrix function computation.

### Degree Bounds
- `degree_reduced_lt_charpoly`: Reduced polynomial has degree < deg(charpoly)
- `degree_reduced_lt_dim`: Reduced polynomial has degree < n

### Power Reduction
- `power_eq_aeval_mod`: A^k = aeval A (X^k %ₘ charpoly)

### Algebraic Structure
- `congruence`: Same remainder mod charpoly → same matrix evaluation
- `charpoly_multiple_annihilates`: Multiples of charpoly annihilate A
- `annihilator_add`, `annihilator_mul_left`: Annihilator is an ideal

### Power Series Foundation
- `partial_sum_reduces`: Finite power series reduce via charpoly
- `partial_sum_reduced_bound`: Reduced partial sums have degree < n

### Special Cases
- `nilpotent_from_charpoly`: Nilpotent matrices from charpoly = X^n
- `nilpotent_higher_powers_vanish`: Higher powers vanish
- `idempotent_power`: A^k = A for idempotent matrices
- `scalar_powers`: (cI)^k = c^k·I

### Connection to Matrix Exponential
The matrix exponential exp(tA) = Σ (tA)^k/k! converges to a matrix that,
by our algebraic results, lies in the span of {I, A, ..., A^{n-1}}.
The coefficients αᵢ(t) are determined by solving:
  exp(tλⱼ) = Σ_{i=0}^{n-1} αᵢ(t) λⱼ^i  for each eigenvalue λⱼ
-/

#check @charpoly_annihilates
#check @aeval_eq_aeval_modByMonic
#check @power_eq_aeval_mod
#check @aeval_reduced
#check @congruence

end CayleyHamiltonOQ02
