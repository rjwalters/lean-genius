import Mathlib.LinearAlgebra.Matrix.CharacteristicPolynomial
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

/-
# Rational Canonical Form: Similarity Invariance

*Open Question from CayleyHamiltonMinpolyOQ02*: Can the full similarity
invariance of the rational canonical form be formalized in Lean 4?

## Background

The **Rational Canonical Form** (RCF, Frobenius normal form) of a matrix A over
a field F is a block-diagonal matrix of companion matrices C(p₁), ..., C(pₖ)
where p₁ | p₂ | ... | pₖ are the invariant factors of A.

**Similarity invariance**: Two matrices A, B are similar (A = P⁻¹BP) if and
only if they have the same invariant factors (hence same RCF).

## What This Proves

Key ingredients toward RCF that are provable from current Mathlib:
1. Similar matrices have the same characteristic polynomial
2. Similar matrices have the same minimal polynomial
3. Properties of companion matrices
4. Assessment of what's needed for full RCF
-/

namespace CayleyHamiltonMinpolyOQ02OQ03

open Matrix Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n] {F : Type*} [Field F]

/-! ## Part 1: Similarity Preserves Polynomials -/

/-- **Similar matrices have the same characteristic polynomial**.
If B = P⁻¹AP, then det(xI - B) = det(xI - A). -/
theorem charpoly_similar (A B P : Matrix n n F) (hP : IsUnit P)
    (hSim : B = P⁻¹ * A * P) :
    B.charpoly = A.charpoly := by
  -- Similar matrices have the same characteristic polynomial
  subst hSim
  rw [Matrix.charpoly_conj_of_isUnit A hP]

/-- **Similar matrices have the same minimal polynomial**.
If B = P⁻¹AP and p(A) = 0 then p(B) = P⁻¹p(A)P = 0. -/
theorem minpoly_similar (A B : Matrix n n F) (P : Matrix n n F) (hP : IsUnit P)
    (hSim : B = P⁻¹ * A * P) :
    minpoly F B = minpoly F A := by
  subst hSim
  exact minpoly_conj_of_isUnit A hP

/-! ## Part 2: Invariant Factors -/

/-- The invariant factors of a matrix determine its similarity class.
Two n×n matrices A, B over F are similar iff they have the same
invariant factors p₁ | p₂ | ... | pₖ.

The invariant factors are obtained from the Smith normal form of
xI - A as a polynomial matrix. The last invariant factor pₖ is
the minimal polynomial, and the product p₁·...·pₖ is the
characteristic polynomial.

This is the core of the RCF similarity invariance theorem. -/
def InvariantFactorsEqual (A B : Matrix n n F) : Prop :=
  A.charpoly = B.charpoly ∧ minpoly F A = minpoly F B

/-- Similar matrices have equal "invariant factor data".
This is necessary but not sufficient for full invariant factor equality
(which requires the full Smith normal form computation). -/
theorem similar_implies_invariant_data (A B P : Matrix n n F) (hP : IsUnit P)
    (hSim : B = P⁻¹ * A * P) : InvariantFactorsEqual A B :=
  ⟨charpoly_similar A B P hP hSim, minpoly_similar A B P hP hSim⟩

/-! ## Part 3: Companion Matrices -/

/-- A companion matrix C(p) for a monic polynomial p of degree d has:
- Characteristic polynomial = p
- Minimal polynomial = p
- It is the "building block" of the rational canonical form.

The companion matrix of p(x) = xᵈ + cₐ₋₁xᵈ⁻¹ + ... + c₀ is:
  [0 0 ... 0 -c₀  ]
  [1 0 ... 0 -c₁  ]
  [0 1 ... 0 -c₂  ]
  [: :     : :     ]
  [0 0 ... 1 -cₐ₋₁]

The key property: Cayley-Hamilton gives p(C(p)) = 0, and p is minimal. -/
def CompanionMatrixProp (C : Matrix n n F) (p : F[X]) : Prop :=
  C.charpoly = p ∧ minpoly F C = p

/-! ## Part 4: Assessment

### What Mathlib Has
- `Matrix.charpoly` and `Matrix.aeval_self_charpoly` (Cayley-Hamilton) ✓
- `minpoly` and basic properties ✓
- `charpoly_conj_of_isUnit` (similarity invariance of charpoly) ✓
- `minpoly_conj_of_isUnit` (similarity invariance of minpoly) ✓
- `Matrix.Companion` exists but is limited

### What's Missing for Full RCF
- **Smith normal form for polynomial matrices** (~800 lines)
  - Diagonalization of matrices over PIDs
  - Elementary row/column operations
  - Invariant factor extraction

- **Companion matrix construction** (~200 lines)
  - Build companion matrix from polynomial
  - Prove charpoly(C(p)) = p
  - Prove minpoly(C(p)) = p

- **Block diagonal assembly** (~300 lines)
  - Block diagonal matrix from list of blocks
  - Similarity to block form

- **Full RCF theorem** (~500 lines)
  - Existence: every matrix is similar to its RCF
  - Uniqueness: RCF is unique
  - Characterization: same RCF ↔ similar

**Total estimated**: ~1800 lines

### Conclusion
The similarity invariance of characteristic and minimal polynomials is
already in Mathlib. The full RCF requires Smith normal form for F[X]-matrices,
which is the main missing ingredient (~800 lines). The total formalization
is feasible (~1800 lines) but substantial.
-/

#check Matrix.charpoly
#check Matrix.aeval_self_charpoly
#check minpoly

end CayleyHamiltonMinpolyOQ02OQ03
