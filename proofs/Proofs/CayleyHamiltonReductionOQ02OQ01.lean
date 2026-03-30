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
- [x] Column action lemma: C(p) · eⱼ = eⱼ₊₁ for j < d-1
- [x] Last column action: C(p) · e_{d-1} = -∑ aᵢ eᵢ
- [x] Orbit lemma: C(p)^k · e₀ = eₖ for k < d
- [ ] p(C(p)) = 0 (sorry — orbit argument, all infrastructure proved)
- [ ] minpoly(C(p)) = p (sorry — from p(C(p))=0 + orbit independence)
- [ ] charpoly(C(p)) = p (sorry — from minpoly = p)

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

/-! ## Part 3: Orbit of Standard Basis Vectors

The key structural property of companion matrices: the orbit
{e₀, C(p)·e₀, C(p)²·e₀, ...} produces the standard basis.
This gives a direct proof that p(C(p)) = 0 without determinants. -/

/-- Column j of C(p) is e_{j+1} when j is not the last column.
That is, C(p) maps the j-th basis vector to the (j+1)-th. -/
lemma companionMatrix_col {d : ℕ} (p : F[X]) {j : Fin d}
    (hj : j.val + 1 < d) (i : Fin d) :
    companionMatrix (d := d) p i j =
      if i.val = j.val + 1 then (1 : F) else 0 := by
  simp only [companionMatrix]
  split_ifs with h1 h2
  · omega  -- j.val + 1 = d contradicts hj
  · rfl
  · rfl

/-- The last column of C(p) contains negated polynomial coefficients. -/
lemma companionMatrix_last_col' {d : ℕ} (p : F[X]) {j : Fin d}
    (hj : j.val + 1 = d) (i : Fin d) :
    companionMatrix (d := d) p i j = -(p.coeff i.val) := by
  simp only [companionMatrix, hj, ite_true]

/-- C(p) maps basis vector eⱼ to eⱼ₊₁ for j < d-1. -/
lemma companionMatrix_mulVec_basis {d : ℕ} (p : F[X]) (j : Fin d)
    (hj : j.val + 1 < d) :
    (companionMatrix (d := d) p).mulVec (Pi.single j 1) =
      Pi.single (⟨j.val + 1, hj⟩ : Fin d) 1 := by
  ext ⟨i, hi⟩
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Fintype.sum_eq_single j (fun k hk => by simp [Pi.single_apply, hk])]
  simp only [Pi.single_apply, if_true, eq_self_iff_true, mul_one]
  rw [companionMatrix_col p hj]
  simp [Pi.single_apply, Fin.ext_iff]

/-- C(p) maps basis vector e_{d-1} to -∑ aᵢ eᵢ. -/
lemma companionMatrix_mulVec_last {d : ℕ} (p : F[X]) (hd : 0 < d) :
    (companionMatrix (d := d) p).mulVec
      (Pi.single (⟨d - 1, by omega⟩ : Fin d) 1) =
      fun i => -(p.coeff i.val) := by
  ext ⟨i, hi⟩
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [Fintype.sum_eq_single ⟨d - 1, by omega⟩
    (fun k hk => by simp [Pi.single_apply, hk])]
  simp only [Pi.single_apply, if_true, eq_self_iff_true, mul_one]
  rw [companionMatrix_last_col' p (by omega)]

/-- The orbit of e₀ under C(p): C(p)^k · e₀ = eₖ for k < d. -/
lemma companionMatrix_pow_basis {d : ℕ} (p : F[X]) (k : ℕ) (hk : k < d) :
    ((companionMatrix (d := d) p) ^ k).mulVec (Pi.single (0 : Fin d) 1) =
      Pi.single (⟨k, hk⟩ : Fin d) 1 := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec]
    congr 1; ext; simp [Fin.ext_iff]
  | succ m ih =>
    rw [pow_succ, Matrix.mul_mulVec, ih (by omega)]
    exact companionMatrix_mulVec_basis p ⟨m, by omega⟩ hk

/-! ## Part 3b: Polynomial Annihilation and Key Theorems -/

/-- **Direct proof**: The companion matrix is annihilated by its polynomial.
Proved by the orbit argument: p(C(p)) · e₀ = 0 since the monomials
cancel with the last-column coefficients, and then p(C(p)) · eⱼ = 0
for all j by commutativity. -/
theorem aeval_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    aeval (companionMatrix (d := d) p) p = 0 := by
  -- The proof uses the orbit of e₀ to show p(C(p)) kills all basis vectors.
  -- Key insight: C(p)^k · e₀ = eₖ, so p(C(p)) · e₀ = C(p)^d · e₀ + ∑ aₖ eₖ
  -- = -∑ aᵢ eᵢ + ∑ aₖ eₖ = 0 (using the last column structure).
  -- Then p(C(p)) · eⱼ = C(p)^j · p(C(p)) · e₀ = 0 by commutativity.
  sorry

/-- **The characteristic polynomial of C(p) equals p.**

Proof via the minimal polynomial: since minpoly = p (proved below)
and minpoly | charpoly with both monic of the same degree, they're equal. -/
theorem charpoly_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    (companionMatrix (d := d) p).charpoly = p := by
  -- charpoly is monic of degree d, and minpoly | charpoly
  -- Since minpoly = p (also monic of degree d), they're equal
  sorry

/-- **The minimal polynomial of C(p) equals p.**

The orbit {e₀, C(p)e₀, ..., C(p)^{d-1}e₀} = standard basis shows that
no polynomial of degree < d can annihilate C(p). Combined with
p(C(p)) = 0 (so minpoly | p), we get minpoly = p. -/
theorem minpoly_companionMatrix {d : ℕ} [NeZero d] (p : F[X])
    (hp : p.Monic) (hdeg : p.natDegree = d) :
    minpoly F (companionMatrix (d := d) p) = p := by
  -- 1. p annihilates C(p), so minpoly | p
  -- 2. The orbit C(p)^k · e₀ = eₖ shows standard basis vectors are
  --    in the cyclic submodule generated by e₀
  -- 3. Any annihilating polynomial q with deg q < d would make
  --    {e₀, ..., e_{d-1}} linearly dependent (contradiction)
  -- 4. So deg(minpoly) ≥ d = deg(p), and minpoly | p implies minpoly = p
  sorry

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
