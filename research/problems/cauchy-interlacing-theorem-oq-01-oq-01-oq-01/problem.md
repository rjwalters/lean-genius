# Problem: Matrix-Level Cauchy Interlacing from the Compression Identity

**Slug**: cauchy-interlacing-theorem-oq-01-oq-01-oq-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{compress}(\text{toEuclideanLin}\, A)\, H \;\cong_U\; \text{toEuclideanLin}\bigl(A.\text{submatrix}\; j.\text{succAbove}\; j.\text{succAbove}\bigr)
$$

so that for a Hermitian $A \in \mathbb{C}^{n\times n}$ with eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ and the principal $(n-1)\times(n-1)$ submatrix $B$ obtained by deleting row and column $j$, with eigenvalues $\mu_1 \ge \dots \ge \mu_{n-1}$, one has the interlacing
$$
\lambda_{k+1} \le \mu_k \le \lambda_k, \qquad 1 \le k \le n-1 .
$$

### Plain Language

The parent gallery entry proves the geometric fact that orthogonally compressing a linear map to the coordinate hyperplane $H = e_j^{\perp}$ yields exactly the principal submatrix of $A$ with row and column $j$ deleted. This problem closes the loop: package that identity into the classical matrix statement that the eigenvalues of the deleted-row-and-column principal submatrix interlace the eigenvalues of $A$.

### Why This Matters

Cauchy interlacing is a workhorse of spectral graph theory, numerical linear algebra, and perturbation theory. Mathlib has the abstract min–max (Courant–Fischer) machinery and now the compression-equals-submatrix bridge, but no user-facing corollary phrased with `Matrix.submatrix` and eigenvalues. Supplying it makes the theorem citable by downstream results such as eigenvalue bounds for graphs, quadrature, and Sturm sequences.

## Known Results

### What's Already Proven

- Orthogonal compression to $e_j^{\perp}$ equals the principal submatrix — parent proof `cauchy-interlacing-theorem-oq-01-oq-01`.
- Courant–Fischer min–max characterization of Hermitian eigenvalues — Mathlib spectral API.
- Interlacing for a self-adjoint operator restricted to a codimension-one subspace — the abstract form underlying the parent entry.

### What's Still Open

- The explicit unitary equivalence `compress (toEuclideanLin A) H ≃ toEuclideanLin (A.submatrix j.succAbove j.succAbove)` as a bundled `LinearIsometryEquiv`.
- The final `Matrix`-level corollary stated with `Matrix.IsHermitian.eigenvalues` and monotone-ordered eigenvalue indices.

### Our Goal

Prove the matrix-level interlacing corollary $\lambda_{k+1} \le \mu_k \le \lambda_k$ for the delete-$j$ principal submatrix, using the compression identity plus the abstract subspace-interlacing theorem, with the isometry $e_{j.\text{succAbove}\, i} \mapsto e_i$ made explicit.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-interlacing-theorem-oq-01-oq-01 | Direct parent: compression equals principal submatrix | orthogonal projection, `toEuclideanLin` |
| cauchy-interlacing-theorem-oq-01 | Abstract subspace interlacing | Courant–Fischer min–max |

## Initial Thoughts

### Potential Approaches

1. **Approach A — build the isometry first**: Construct the `LinearIsometryEquiv` from `EuclideanSpace ℂ (Fin (n-1))` onto $H = e_j^{\perp}$ sending $e_i \mapsto e_{j.\text{succAbove}\, i}$, then transport eigenvalues through it.
   - Why it might work: `Fin.succAbove` is exactly the "skip index $j$" embedding, so the basis correspondence is essentially definitional.
   - Risk: bookkeeping between `orthogonalProjection`, `Submodule.subtypeₗᵢ`, and `toEuclideanLin` may need several bridging `ext`/`simp` lemmas.

2. **Approach B — go through quadratic forms**: Show the Rayleigh quotients of $B$ on $\mathbb{C}^{n-1}$ coincide with those of $A$ restricted to $H$, then apply min–max directly without an explicit unitary.
   - Why it might work: avoids bundling the isometry; only needs equality of Rayleigh quotients on matching subspaces.
   - Risk: min–max index alignment ($k$ versus $k+1$) is error-prone; still needs the compression identity.

### Key Difficulties

- Aligning Mathlib's eigenvalue ordering conventions with the interlacing indices $k$ and $k+1$.
- Cleanly transporting the self-adjoint structure across the isometry so `IsHermitian` is preserved on the submatrix.

### What Would a Proof Need?

- Key lemma 1: `compress (toEuclideanLin A) H` is unitarily equivalent to `toEuclideanLin (A.submatrix j.succAbove j.succAbove)` (bundled isometry).
- Key lemma 2: eigenvalues are invariant under unitary equivalence (available in Mathlib).
- Technical requirements: `Fin.succAbove` basis embedding, `orthogonalProjection` API, Courant–Fischer with correct index conventions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard geometric step (compression equals submatrix) is already done in the parent.
- Remaining work is largely glue: an explicit isometry plus an index-careful application of an existing min–max theorem.
- Similar unitary-transport-of-eigenvalues arguments already appear in Mathlib's spectral theorem development.

**Estimated Effort**:
- Exploration: 1–2 days to map the exact Mathlib API surface.
- If tractable: 3–5 days for the bundled isometry and final corollary.
- If hard: index-convention friction could extend this.

## References

### Papers
- Horn & Johnson, *Matrix Analysis* (2nd ed., 2013), Section 4.3 — Cauchy interlacing and eigenvalues of principal submatrices.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/ — `Matrix.IsHermitian.eigenvalues`, `EuclideanSpace`, `toEuclideanLin`.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.Spectrum` — spectral theorem and eigenvalue min–max.
- `Mathlib.LinearAlgebra.Matrix.Hermitian` — Hermitian matrix eigenvalue API.
- `Fin.succAbove` — the delete-index embedding.

## Metadata

```yaml
tags:
  - linear-algebra
  - spectral
  - hermitian
  - cauchy-interlacing
  - principal-submatrix
  - eigenvalues
related_proofs:
  - cauchy-interlacing-theorem-oq-01-oq-01
  - cauchy-interlacing-theorem-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
