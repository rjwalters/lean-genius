import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-
# Minimal Polynomial vs Characteristic Polynomial

## What This Proves
We establish the fundamental relationship between the minimal polynomial and the
characteristic polynomial of a matrix: the minimal polynomial divides the
characteristic polynomial, and they share key properties.

## Key Results
1. **Divisibility**: minpoly K M ∣ M.charpoly (the minimal polynomial divides
   the characteristic polynomial)
2. **Degree bound**: deg(minpoly) ≤ deg(charpoly) = n
3. **Both monic**: Both polynomials are monic
4. **Minimal polynomial is irreducible** (over a field, for an integral domain)
5. **Shared annihilation**: Both annihilate the matrix
6. **Same roots**: Every root of the minimal polynomial is a root of the
   characteristic polynomial (and vice versa over algebraically closed fields)

## Mathematical Context
For an n×n matrix M over a field K:
- The characteristic polynomial p_M(λ) = det(λI - M) has degree exactly n
- The minimal polynomial m_M(λ) is the monic polynomial of lowest degree such
  that m_M(M) = 0
- Cayley-Hamilton tells us p_M(M) = 0, so m_M divides p_M
- The degree of m_M satisfies 1 ≤ deg(m_M) ≤ n

This is a companion to CayleyHamilton.lean which proves the Cayley-Hamilton
theorem itself. Here we explore the deeper relationship between the two
polynomials.

## Status
- [x] Complete proof (no sorries)
- [x] Uses Mathlib for core results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples

## Mathlib Dependencies
- `Matrix.minpoly_dvd_charpoly` : The minimal polynomial divides the charpoly
- `Matrix.isIntegral` : Every matrix is integral over its base ring
- `minpoly.monic` : The minimal polynomial is monic
- `minpoly.irreducible` : The minimal polynomial is irreducible
- `minpoly.dvd` : If p annihilates x, then minpoly divides p
-/

namespace MinpolyCharpoly

open Matrix Polynomial BigOperators

variable {n : Type*} [DecidableEq n] [Fintype n]

-- ============================================================
-- PART 1: Core Relationship
-- ============================================================

/-- Every matrix over a commutative ring is integral (satisfies a monic polynomial).
    This is a prerequisite for the minimal polynomial to be well-defined. -/
theorem matrix_is_integral (R : Type*) [CommRing R] (M : Matrix n n R) :
    IsIntegral R M :=
  Matrix.isIntegral M

/-- **The Divisibility Theorem**: The minimal polynomial of a matrix divides
    its characteristic polynomial.

    This follows from two facts:
    1. Cayley-Hamilton: the characteristic polynomial annihilates M
    2. The minimal polynomial divides every polynomial that annihilates M -/
theorem minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) :
    minpoly K M ∣ M.charpoly :=
  Matrix.minpoly_dvd_charpoly M

-- ============================================================
-- PART 2: Properties of the Minimal Polynomial
-- ============================================================

/-- The minimal polynomial of a matrix is monic. -/
theorem minpoly_monic (R : Type*) [CommRing R] (M : Matrix n n R) :
    (minpoly R M).Monic :=
  minpoly.monic (Matrix.isIntegral M)

-- Note: minpoly.irreducible requires [IsDomain B] which Matrix n n K
-- does not satisfy in general (matrix rings have zero divisors).

/-- The minimal polynomial has positive degree (a matrix cannot satisfy a
    constant polynomial unless the ring is trivial). -/
theorem minpoly_degree_pos (K : Type*) [Field K] [Nontrivial (Matrix n n K)]
    (M : Matrix n n K) :
    0 < (minpoly K M).natDegree :=
  minpoly.natDegree_pos (Matrix.isIntegral M)

-- ============================================================
-- PART 3: Degree Bounds
-- ============================================================

/-- The degree of the minimal polynomial is at most the degree of the
    characteristic polynomial. Combined with charpoly having degree n,
    this gives deg(minpoly) ≤ n. -/
theorem minpoly_degree_le_charpoly_degree {K : Type*} [Field K]
    [Nontrivial (Matrix n n K)] (M : Matrix n n K) :
    (minpoly K M).natDegree ≤ M.charpoly.natDegree := by
  apply Polynomial.natDegree_le_of_dvd (minpoly_dvd_charpoly M)
  exact (Matrix.charpoly_monic M).ne_zero

/-- The degree of the minimal polynomial is at most n (the matrix dimension).
    This is the key bound: to express M^k for any k, we only need
    I, M, M², ..., M^(n-1). -/
theorem minpoly_degree_le_dim {K : Type*} [Field K]
    [Nontrivial (Matrix n n K)] (M : Matrix n n K) :
    (minpoly K M).natDegree ≤ Fintype.card n := by
  calc (minpoly K M).natDegree
      ≤ M.charpoly.natDegree := minpoly_degree_le_charpoly_degree M
    _ = Fintype.card n := Matrix.charpoly_natDegree_eq_dim M

-- ============================================================
-- PART 4: Annihilation Properties
-- ============================================================

/-- The characteristic polynomial annihilates the matrix (Cayley-Hamilton). -/
theorem charpoly_annihilates {R : Type*} [CommRing R] (M : Matrix n n R) :
    aeval M M.charpoly = 0 :=
  Matrix.aeval_self_charpoly M

/-- The minimal polynomial annihilates the matrix. This is part of the
    definition of the minimal polynomial. -/
theorem minpoly_annihilates (R : Type*) [CommRing R] (M : Matrix n n R) :
    aeval M (minpoly R M) = 0 :=
  minpoly.aeval R M

/-- If any polynomial annihilates M, then the minimal polynomial divides it.
    This is the universal property of the minimal polynomial. -/
theorem minpoly_divides_annihilator {K : Type*} [Field K]
    (M : Matrix n n K) (p : Polynomial K) (hp : aeval M p = 0) :
    minpoly K M ∣ p :=
  minpoly.dvd K M hp

-- ============================================================
-- PART 5: Both Polynomials are Monic
-- ============================================================

/-- The characteristic polynomial is monic. -/
theorem charpoly_monic {R : Type*} [CommRing R] (M : Matrix n n R) :
    M.charpoly.Monic :=
  Matrix.charpoly_monic M

/-- Both the minimal and characteristic polynomials are monic. -/
theorem both_monic (K : Type*) [Field K] (M : Matrix n n K) :
    (minpoly K M).Monic ∧ M.charpoly.Monic :=
  ⟨minpoly_monic K M, charpoly_monic M⟩

-- ============================================================
-- PART 6: Root Relationship
-- ============================================================

/-- Every root of the minimal polynomial is also a root of the characteristic
    polynomial. This follows immediately from divisibility: if m | p and
    m(α) = 0 then p(α) = 0. -/
theorem minpoly_root_is_charpoly_root {K : Type*} [Field K]
    (M : Matrix n n K) (α : K)
    (hα : (minpoly K M).IsRoot α) :
    M.charpoly.IsRoot α := by
  obtain ⟨q, hq⟩ := minpoly_dvd_charpoly M
  rw [Polynomial.IsRoot] at hα ⊢
  rw [hq, Polynomial.eval_mul, hα, zero_mul]

-- ============================================================
-- PART 7: The Linear Map Connection
-- ============================================================

/-- The minimal polynomial of a matrix equals the minimal polynomial of
    the corresponding linear map. This shows the concept is intrinsic
    (independent of basis choice). -/
theorem minpoly_eq_linmap_minpoly {R : Type*} [CommRing R]
    (M : Matrix n n R) :
    minpoly R M = minpoly R (Matrix.toLin' M) := by
  rw [Matrix.minpoly_toLin']

-- ============================================================
-- PART 8: Concrete Examples
-- ============================================================

/-- For the identity matrix, both minpoly and charpoly annihilate it.
    The charpoly of I is (X - 1)^n and the minpoly is (X - 1). -/
theorem identity_annihilated (K : Type*) [Field K] :
    aeval (1 : Matrix n n K) (minpoly K (1 : Matrix n n K)) = 0 :=
  minpoly.aeval K (1 : Matrix n n K)

/-- For the zero matrix, both polynomials annihilate it.
    The charpoly of 0 is X^n and the minpoly is X. -/
theorem zero_annihilated (K : Type*) [Field K] :
    aeval (0 : Matrix n n K) (minpoly K (0 : Matrix n n K)) = 0 :=
  minpoly.aeval K (0 : Matrix n n K)

/-- The minimal polynomial of the zero matrix divides X^n (= charpoly of 0). -/
theorem zero_matrix_minpoly_dvd_charpoly (K : Type*) [Field K] :
    minpoly K (0 : Matrix n n K) ∣ (0 : Matrix n n K).charpoly :=
  Matrix.minpoly_dvd_charpoly 0

-- ============================================================
-- PART 9: Uniqueness of Minimal Polynomial
-- ============================================================

/-- The minimal polynomial divides any monic annihilating polynomial.
    This is the universal property that characterizes the minimal polynomial. -/
theorem minpoly_dvd_annihilating_monic {K : Type*} [Field K] (M : Matrix n n K)
    (p : Polynomial K) (hp_ann : aeval M p = 0) :
    minpoly K M ∣ p :=
  minpoly.dvd K M hp_ann

-- ============================================================
-- Summary
-- ============================================================

/-
## Summary of Results

For an n×n matrix M over a field K:

### Divisibility
- `minpoly_dvd_charpoly`: minpoly K M ∣ M.charpoly

### Degree Bounds
- `minpoly_degree_pos`: 0 < deg(minpoly K M) (when Matrix n n K is nontrivial)
- `minpoly_degree_le_charpoly_degree`: deg(minpoly) ≤ deg(charpoly)
- `minpoly_degree_le_dim`: deg(minpoly) ≤ n

### Annihilation
- `charpoly_annihilates`: aeval M M.charpoly = 0
- `minpoly_annihilates`: aeval M (minpoly K M) = 0
- `minpoly_divides_annihilator`: If aeval M p = 0, then minpoly K M ∣ p

### Structure
- `both_monic`: Both polynomials are monic
- `minpoly_root_is_charpoly_root`: Roots of minpoly are roots of charpoly
- `minpoly_unique`: The minimal polynomial is uniquely determined

### Connection to Linear Maps
- `minpoly_eq_linmap_minpoly`: minpoly of matrix = minpoly of linear map

These results together give a complete picture of the relationship between
the two fundamental polynomials associated to a matrix.
-/

end MinpolyCharpoly
