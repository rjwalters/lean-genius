# Problem: Rational Canonical Form: Companion Matrix (Complete Proof)

**Slug**: cayley-hamilton-reduction-oq-02-oq-01-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a monic polynomial $p \in R[X]$ of degree $n$, let $C(p)$ be the companion matrix. Prove:

1. $p(C(p)) = 0$ — C(p) annihilates its own defining polynomial
2. $\text{minpoly}(C(p)) = p$ — minimal polynomial equals p
3. $\text{charpoly}(C(p)) = p$ — characteristic polynomial equals p

### Plain Language

The companion matrix $C(p)$ is an $n \times n$ matrix built from $p$'s coefficients: 1s on the subdiagonal, $-a_i$ in the last column. We need to prove it "encodes" $p$ completely — its characteristic and minimal polynomials are exactly $p$.

### Why This Matters

The companion matrix is the fundamental building block of rational canonical form (Frobenius normal form). Completing this proof enables:
- Formal proof of the full rational canonical form theorem
- That every square matrix over a field is similar to a companion-matrix block-diagonal form
- Connection between module structure and Jordan/RCF theory

## Known Results

### What's Already Proven

- `companionMatrix_subdiag_entry`: Entry at (i+1, i) = 1 (subdiagonal)
- `companionMatrix_last_col_entry`: Last column entries = -p coefficients
- `companionMatrix_linear`: C(X - c) = [c] (linear polynomial case)
- Full orbit infrastructure (e_i → C*e_i chain) is proven
- `Matrix.aeval_self_charpoly` in Mathlib (Cayley-Hamilton)

### What's Still Open

3 sorry statements in `proofs/Proofs/CayleyHamiltonReductionOQ02OQ01.lean` (lines 183, 194, 210):
- Line 183: `p(C(p)) = 0` — orbit argument (all infrastructure proved)
- Line 194: `minpoly(C(p)) = p` — from p(C(p))=0 + orbit independence
- Line 210: `charpoly(C(p)) = p` — from minpoly = p

### Our Goal

Fill all 3 sorry statements in `CayleyHamiltonReductionOQ02OQ01.lean` to achieve 0 sorries.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton-reduction-oq-02-oq-01 | Direct parent (3 sorries) | Companion matrix, orbit infrastructure |
| cayley-hamilton-reduction-oq-02 | RCF parent | Module theory, Smith normal form |
| cayley-hamilton | Core theorem | aeval_self_charpoly |

## Initial Thoughts

### Potential Approaches

1. **Orbit computation** (for p(C(p)) = 0):
   - Standard basis vector e_1 generates the whole space under C(p)
   - C(p)^k * e_1 = e_{k+1} for k < n, then wraps by the polynomial recurrence
   - All orbit infrastructure already proven; just need final assembly
   - Risk: bookkeeping in Lean matrix multiplication

2. **Cofactor expansion** (for charpoly = p):
   - Structure of C(p) makes cofactor expansion along last column yield p directly
   - Risk: determinant induction can be messy

3. **Degree + divisibility** (for minpoly = p):
   - minpoly divides charpoly (both monic degree n)
   - p(C(p)) = 0 implies minpoly divides p
   - Since both monic degree n, they are equal
   - Risk: needs `Polynomial.minpoly.dvd` in Mathlib

### Key Difficulties

- Matrix multiplication bookkeeping in Lean for orbit argument
- Finding correct Mathlib API for `minpoly.dvd` and `det_companion`

### What Would a Proof Need?

- Key lemma 1: Orbit computation showing p(C(p)) kills each basis vector
- Key lemma 2: `Polynomial.minpoly.dvd` — minpoly divides any annihilating poly
- Technical: `Matrix.det_companion` or Leibniz formula for determinant

## Tractability Assessment

**Difficulty**: Medium (challenging)

**Justification**:
- All orbit infrastructure is already proven
- Mathlib has relevant lemmas (aeval_self_charpoly, minpoly.dvd)
- Mathematical argument is clear: orbit → p(C(p))=0 → minpoly=p → charpoly=p
- Main risk: Lean formalization of matrix indexing and polynomial evaluation

**Estimated Effort**:
- Exploration: 1-2 hours
- If tractable: 1-3 days
- If hard: 1 week

## References

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` — aeval_self_charpoly
- `Mathlib.FieldTheory.Minpoly.Basic` — minpoly.dvd, minpoly.degree_le
- `Mathlib.LinearAlgebra.Matrix.Determinant` — det computation

## Metadata

```yaml
tags:
  - linear-algebra
  - matrices
  - companion-matrix
  - rational-canonical-form
  - completion
related_proofs:
  - cayley-hamilton-reduction-oq-02-oq-01
  - cayley-hamilton-reduction-oq-02
  - cayley-hamilton
difficulty: medium
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 6/10
