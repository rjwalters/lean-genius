# Problem: Sylvester Matrix Interpolation via Frobenius Covariants

**Slug**: cayley-hamilton-oq-02-oq-02
**Created**: 2026-06-18
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $A$ be an $n \times n$ matrix over a field (or algebraically closed field) with **distinct** eigenvalues $\lambda_1, \dots, \lambda_m$. Define the Frobenius covariants

$$
Z_j \;=\; \prod_{i \ne j} \frac{A - \lambda_i I}{\lambda_j - \lambda_i}.
$$

Then for any function $f$ defined on the spectrum (in particular any polynomial), Sylvester's formula holds:

$$
f(A) \;=\; \sum_{j=1}^{m} f(\lambda_j)\, Z_j,
$$

with the $Z_j$ being the spectral projections: $Z_j Z_k = \delta_{jk} Z_j$, $\sum_j Z_j = I$, and $A = \sum_j \lambda_j Z_j$.

### Plain Language

For a diagonalizable matrix, any (matrix) function can be written as a weighted sum of fixed "projection" matrices $Z_j$ — one per eigenvalue — weighted by the scalar values $f(\lambda_j)$. The $Z_j$ are Lagrange-interpolation polynomials in $A$ and act as projectors onto the eigenspaces. We want a formal proof of this representation.

### Why This Matters

Sylvester's formula is the explicit, computation-ready form of the spectral theorem / matrix-function calculus underlying `cayley-hamilton-oq-02` ("Computing Matrix Functions via Cayley-Hamilton Reduction"). It connects Lagrange interpolation, the Cayley-Hamilton reduction of $f(A)$ to a degree-$<n$ polynomial, and spectral projections into one clean identity.

## Known Results

### What's Already Proven

- `cayley-hamilton-oq-02` ("Computing Matrix Functions via Cayley-Hamilton Reduction") — reduces $f(A)$ to a polynomial of degree $< n$ in $A$.
- Mathlib `Matrix.charpoly`, `Matrix.aeval_self_charpoly` (Cayley-Hamilton), and `LinearMap`/`Module.End` eigenspace decompositions.

### What's Still Open

- The explicit Frobenius-covariant representation and the projector identities $Z_j Z_k = \delta_{jk} Z_j$, $\sum_j Z_j = I$.
- Sylvester's formula $f(A) = \sum_j f(\lambda_j) Z_j$ as a stated theorem.

### Our Goal

Prove Sylvester's formula in the distinct-eigenvalue (diagonalizable) case: define $Z_j$ via Lagrange basis polynomials evaluated at $A$, prove the projector relations from $\prod_i (A - \lambda_i I) = 0$ (minimal polynomial splits with simple roots), and conclude the interpolation identity for polynomials $f$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cayley-hamilton-oq-02 | Reduces $f(A)$ to degree-$<n$ polynomial; same matrix-function setting | Cayley-Hamilton, polynomial reduction |
| cayley-hamilton (parent family) | Characteristic/minimal polynomial machinery | charpoly, minpoly |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Lagrange interpolation at the spectrum**: define $Z_j = L_j(A)$ for the Lagrange basis polynomials $L_j$ of the nodes $\lambda_j$; prove $\sum_j Z_j = I$ (since $\sum_j L_j = 1$) and idempotency/orthogonality from the minimal polynomial $\prod_i(X-\lambda_i)$ annihilating $A$. For polynomial $f$, $f(A) = \sum_j f(\lambda_j) L_j(A)$ follows from $f \equiv \sum_j f(\lambda_j) L_j \pmod{\text{minpoly}}$. Risk: assembling the polynomial-congruence step in `Polynomial (Matrix _ _)` / `aeval`.
2. **Approach B — eigenspace projection**: build $Z_j$ as projections onto eigenspaces and verify the formula on a diagonalizing basis. Risk: requires explicit diagonalization data.

### Key Difficulties

- The minimal-polynomial-splits-with-simple-roots hypothesis and feeding it to `aeval`.
- Identifying $L_j(A)$ as genuine projections (idempotent, orthogonal, summing to $I$).

### What Would a Proof Need?

- Lagrange basis polynomials over the distinct eigenvalues and `aeval A` of them.
- The annihilation $\prod_i (A - \lambda_i I) = 0$ (squarefree minimal polynomial).
- Polynomial congruence: $f \equiv \sum_j f(\lambda_j) L_j$ modulo the minimal polynomial, transported through `aeval`.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- Cayley-Hamilton and `aeval` are in Mathlib and the parent already reduces $f(A)$ to polynomials.
- The Lagrange-interpolation-modulo-minpoly argument is standard but needs careful `Polynomial`/`aeval` plumbing.
- Restricting to distinct eigenvalues avoids generalized-eigenspace complications.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks
- If hard (repeated-eigenvalue generalization attempted): 3–4 weeks

## References

### Papers
- R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis* — Sylvester's formula and Frobenius covariants.

### Online Resources
- Standard matrix-analysis references for matrix functions and spectral projections.

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Charpoly.*`, `Matrix.aeval_self_charpoly` — Cayley-Hamilton.
- `Mathlib.LinearAlgebra.Lagrange` — Lagrange interpolation basis polynomials.
- `Mathlib.RingTheory.Polynomial.*`, `Polynomial.aeval` — evaluating polynomials at a matrix.

## Metadata

```yaml
tags:
  - linear-algebra
  - cayley-hamilton
  - matrix-functions
  - spectral-projection
related_proofs:
  - cayley-hamilton-oq-02
difficulty: high
source: proof-suggestion
created: 2026-06-18
```
