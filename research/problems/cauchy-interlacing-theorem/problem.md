# Problem: Cauchy Interlacing Theorem for Hermitian Matrices

**Slug**: cauchy-interlacing-theorem
**Created**: 2026-06-15T12:01:03-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Let } A \in \mathbb{C}^{n\times n} \text{ be Hermitian with eigenvalues } \lambda_1 \le \cdots \le \lambda_n,
$$
$$
\text{and let } B \text{ be a principal } (n-1)\times(n-1) \text{ submatrix with eigenvalues } \mu_1 \le \cdots \le \mu_{n-1}.
$$
$$
\text{Then } \lambda_k \le \mu_k \le \lambda_{k+1} \quad (1 \le k \le n-1).
$$

### Plain Language

If you delete one row and the matching column from a symmetric/Hermitian matrix, the
eigenvalues of the smaller matrix sit between consecutive eigenvalues of the original.
The spectra "interlace."

### Why This Matters

Interlacing is a cornerstone of spectral graph theory (eigenvalue bounds for vertex-deleted
subgraphs), numerical linear algebra (eigenvalue tracking, the divide-and-conquer eigensolver),
and the theory of orthogonal polynomials (roots of consecutive members interlace). It is the
prototype of a large family of interlacing/monotonicity results and underlies the recent
Marcus–Spielman–Srivastava resolution of the Kadison–Singer problem.

## Known Results

### What's Already Proven

- Spectral theorem for Hermitian matrices — `Matrix.IsHermitian.spectral_theorem` (Mathlib)
- Sorted real eigenvalues exist — `Matrix.IsHermitian.eigenvalues` (Mathlib)
- Rayleigh quotient bounds for extreme eigenvalues — partial coverage in Mathlib

### What's Still Open

- A Courant–Fischer min-max characterization of the k-th eigenvalue is not packaged in Mathlib in a form directly usable here.
- The interlacing inequality itself is absent from Mathlib.

### Our Goal

Prove the one-step interlacing inequality $\lambda_k \le \mu_k \le \lambda_{k+1}$ for a principal
$(n-1)\times(n-1)$ submatrix, ideally via a Courant–Fischer min-max argument restricted to the
codimension-one coordinate subspace. The general "delete m rows" version is a stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| minpoly-charpoly-oq-01 | spectral identities for structured matrices | charpoly, eigenvalues |
| cayley-hamilton-cyclic-vector-all-fields-oq-02 | eigenstructure of matrices/operators | minimal polynomial, cyclic vectors |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Courant–Fischer min-max**: Express $\lambda_k = \min_{\dim S = k}\max_{x\in S}\langle Ax,x\rangle/\langle x,x\rangle$ and restrict test subspaces to those inside the codimension-one coordinate hyperplane defining $B$.
   - Why it might work: gives both inequalities symmetrically; standard textbook route.
   - Risk: needs a min-max lemma that may have to be built from scratch in Mathlib.

2. **Approach B — Cauchy's eigenvalue interlacing via the secular equation**: relate $\det(A - xI)$ and $\det(B - xI)$ through the rank-one bordering and sign-change counting.
   - Why it might work: explicit determinant identity, close to Mathlib's `Matrix.det` API.
   - Risk: sign-counting / intermediate value bookkeeping is fiddly to formalize.

### Key Difficulties

- Mathlib lacks a ready-made Courant–Fischer min-max statement for the k-th eigenvalue.
- Indexing the sorted eigenvalues and matching `Fin n` vs `Fin (n-1)` cleanly.

### What Would a Proof Need?

- Key lemma 1: min-max (Courant–Fischer) characterization of sorted Hermitian eigenvalues.
- Key lemma 2: dimension-counting for the intersection of a k-dimensional subspace with a codimension-one hyperplane.
- Technical requirements: `Matrix.IsHermitian` spectral API, inner-product-space lemmas, `Finset`/`Fin` reindexing.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is classical and self-contained; the obstacle is missing Mathlib scaffolding (min-max), not deep theory.
- Mathlib's Hermitian spectral theorem and eigenvalue API provide a real starting point.
- The min-max lemma, once built, is independently reusable (Weyl inequalities, monotonicity).

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1-2 weeks
- If hard: unknown (if min-max must be developed in full generality)

## References

### Papers
- Cauchy, "Sur l'équation à l'aide de laquelle on détermine les inégalités séculaires" (1829) — original interlacing.
- Horn & Johnson, *Matrix Analysis*, 2nd ed., §4.3 — modern statement and proof.

### Online Resources
- Tao, "254A notes: interlacing" — min-max derivation of Cauchy interlacing.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Spectrum` — `Matrix.IsHermitian.eigenvalues`, spectral theorem.
- `Mathlib.Analysis.InnerProductSpace.Rayleigh` — Rayleigh quotient and extreme eigenvalues.

## Metadata

```yaml
tags:
  - linear-algebra
  - spectral-theory
  - eigenvalues
related_proofs:
  - minpoly-charpoly-oq-01
  - cayley-hamilton-cyclic-vector-all-fields-oq-02
difficulty: medium
source: gallery-gap
created: 2026-06-15T12:01:03-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
