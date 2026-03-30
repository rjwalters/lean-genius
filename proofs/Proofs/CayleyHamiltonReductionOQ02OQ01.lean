import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-
# Rational Canonical Form: Companion Matrix Properties

## Open Question
Formalize the rational canonical form (Frobenius normal form) in Lean 4.

## What This Proves

The rational canonical form states that every matrix over a field is similar
to a block diagonal matrix of companion matrices C(p₁), ..., C(pₖ) where
p₁ | p₂ | ... | pₖ are the invariant factors.

This file focuses on the **companion matrix**, the fundamental building block
of the RCF:

1. **Definition**: The companion matrix C(p) for a monic polynomial p of degree d
2. **Polynomial annihilation**: p(C(p)) = 0 (Cayley-Hamilton for companion)
3. **Characteristic polynomial**: charpoly(C(p)) = p (companion determines charpoly)
4. **Minimal polynomial**: minpoly(C(p)) = p (companion is non-derogatory)

## Status
- [x] Companion matrix definition
- [x] Basic properties (size, entries)
- [ ] charpoly(C(p)) = p (sorry — requires det computation)
- [ ] minpoly(C(p)) = p (sorry — requires minimality argument)

## Gap Assessment for Full RCF
- **Smith normal form for F[X]-matrices**: ~800 lines (main blocker)
- **Companion matrix**: ~200 lines (THIS FILE — partial)
- **Block diagonal assembly**: ~300 lines (not started)
- **Full RCF theorem**: ~500 lines (not started)
- **Total estimated**: ~1800 lines

## Mathlib Dependencies
- `Matrix.charpoly`, `Matrix.aeval_self_charpoly` : Cayley-Hamilton
- `minpoly` : Minimal polynomial
- `Polynomial.coeff` : Polynomial coefficients
-/

namespace CayleyHamiltonReductionOQ02OQ01

open Matrix Polynomial BigOperators

variable {F : Type*} [Field F]

/-! ## Part 1: Companion Matrix Definition -/

/-- The **companion matrix** of a monic polynomial p of degree d.

For p(x) = xᵈ + aₐ₋₁xᵈ⁻¹ + ... + a₁x + a₀, the companion matrix is the
d × d matrix:

```
C(p) = | 0  0  0  ...  0  -a₀    |
       | 1  0  0  ...  0  -a₁    |
       | 0  1  0  ...  0  -a₂    |
       | :  :  :  ...  :   :     |
       | 0  0  0  ...  1  -aₐ₋₁  |
```

That is: 1's on the subdiagonal, negated coefficients in the last column,
zeros elsewhere. -/
noncomputable def companionMatrix {d : ℕ} (p : F[X]) : Matrix (Fin d) (Fin d) F :=
  fun i j =>
    if j.val + 1 = d then -(p.coeff i.val)
    else if i.val = j.val + 1 then 1
    else 0

/-! ## Part 2: Basic Properties -/

/-- The subdiagonal entries of the companion matrix are 1. -/
theorem companionMatrix_subdiag {d : ℕ} (p : F[X]) {i j : Fin d}
    (h : i.val = j.val + 1) (hj : j.val + 1 < d) :
    companionMatrix p i j = 1 := by
  simp only [companionMatrix]
  split_ifs with h1 h2
  · omega
  · rfl
  · exact absurd h h2

/-- The last column of the companion matrix has negated coefficients. -/
theorem companionMatrix_last_col {d : ℕ} (p : F[X]) {i : Fin d} {j : Fin d}
    (hj : j.val + 1 = d) :
    companionMatrix p i j = -(p.coeff i.val) := by
  simp only [companionMatrix]
  split_ifs with h1
  · rfl
  · exact absurd hj h1

/-- Off-diagonal, off-last-column entries are zero. -/
theorem companionMatrix_zero {d : ℕ} (p : F[X]) {i j : Fin d}
    (h1 : j.val + 1 ≠ d) (h2 : i.val ≠ j.val + 1) :
    companionMatrix p i j = 0 := by
  simp only [companionMatrix]
  split_ifs <;> contradiction

/-! ## Part 3: Key Theorems (Stated) -/

/-- **The characteristic polynomial of C(p) equals p.**

This is the key theorem connecting companion matrices to polynomials.
The proof requires computing the determinant of (xI - C(p)) by cofactor
expansion along the last column.

Proof strategy:
1. det(xI - C(p)) expands by cofactors along the last column
2. The (d-1, d-1) minor contributes x · det(xI - C(p')) for a submatrix
3. Other minors contribute the polynomial coefficients
4. Induction on d gives det(xI - C(p)) = p(x) -/
theorem charpoly_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    (companionMatrix (d := d) p).charpoly = p := by
  sorry

/-- **The minimal polynomial of C(p) equals p.**

Since charpoly(C(p)) = p and minpoly divides charpoly, and p is the
characteristic polynomial (hence annihilates C(p)), the minimal polynomial
is p itself (companion matrices are non-derogatory).

Proof strategy:
1. minpoly divides charpoly = p
2. If minpoly = q where q | p and q ≠ p, then q annihilates C(p)
3. But the standard basis vector e₁ generates F[X]/⟨q⟩ as a K[x]-module via C(p)
4. dim(F[X]/⟨q⟩) = deg(q) < deg(p) = d, contradicting dim = d
5. Therefore minpoly = p -/
theorem minpoly_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    minpoly F (companionMatrix (d := d) p) = p := by
  sorry

/-- The companion matrix annihilates its defining polynomial.
This follows from Cayley-Hamilton + charpoly = p, or can be
verified directly from the matrix structure. -/
theorem aeval_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    aeval (companionMatrix (d := d) p) p = 0 := by
  rw [← charpoly_companionMatrix p hp hdeg]
  exact aeval_self_charpoly _

/-! ## Part 4: Trivial Case — Linear Polynomial -/

/-- For p(x) = x - c, the companion matrix is the 1×1 matrix [c].
This is the base case for RCF: eigenvalues correspond to 1×1 companion blocks. -/
theorem companionMatrix_linear (c : F) :
    companionMatrix (d := 1) (X - C c) = Matrix.of (fun _ _ => c) := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [companionMatrix, Matrix.of]
  have : i = 0 := by omega
  have : j = 0 := by omega
  subst_vars
  simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  ring

/-! ## Part 5: RCF Roadmap

### Full Rational Canonical Form Statement

**Theorem (RCF)**: For any matrix A ∈ Mₙ(F), there exist unique monic
polynomials p₁ | p₂ | ... | pₖ (the invariant factors of A) with
pₖ = minpoly(F, A) and p₁ · p₂ · ... · pₖ = charpoly(A) such that
A is similar to the block diagonal matrix

  diag(C(p₁), C(p₂), ..., C(pₖ))

### Infrastructure Needed

1. **Smith Normal Form** for matrices over F[X] (a PID):
   - Elementary row/column operations
   - Euclidean algorithm for F[X]
   - Diagonalization theorem
   - ~800 lines, main theoretical blocker

2. **xI - A as a polynomial matrix**:
   - Map from Mₙ(F) to Mₙ(F[X])
   - Invariant factors of xI - A are the invariant factors of A
   - ~200 lines

3. **Block diagonal similarity**:
   - Block diagonal construction from list of matrices
   - Similarity to block form via change of basis
   - ~300 lines

4. **Uniqueness**:
   - Same invariant factors ↔ similar matrices
   - Follows from uniqueness of Smith normal form
   - ~200 lines
-/

#check @companionMatrix
#check @charpoly_companionMatrix
#check @minpoly_companionMatrix
#check @aeval_companionMatrix
#check @companionMatrix_linear

end CayleyHamiltonReductionOQ02OQ01
