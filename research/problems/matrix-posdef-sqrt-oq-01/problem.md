# Problem: Positive semidefinite square root: the unique PSD √A with √A·√A = A

## Statement

### Plain Language
AVAILABLE: every positive semidefinite matrix A over RCLike (ℝ or ℂ) has a unique positive semidefinite square root √A satisfying √A * √A = A; √A is itself Hermitian and PSD, and the square root is unique among PSD matrices.

### Formal Statement
$$
\text{(formal statement to be added)}
$$

## Classification

```yaml
tier: A
significance: 8
tractability: 6
tags:
  - linear-algebra
  - matrix
  - positive-semidefinite
  - square-root
  - hermitian
  - spectral-theorem
  - polar-decomposition
  - seeker-selected
  - research
```

**Significance**: 8/10
**Tractability**: 6/10

## Why This Matters

1. **Research value** - AVAILABLE: every positive semidefinite matrix A over RCLike (ℝ or ℂ) has a unique positive semidefinite square root √A satisfying √A * √A = A; √A is itself Hermitian and PSD, and the square root is unique among PSD matrices

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| det-conjugate-transpose-oq-01 | Sibling complex-matrix structure (adjoint/determinant); this entry's det shadow det(√A)² = det A connects the PSD square root to the determinant invariant. |

## Status

**COMPLETED** — verified 0-axiom gallery entry `proofs/Proofs/MatrixPosDefSqrtOQ01.lean`
(9 theorems, 0 sorries, 0 axioms, no `native_decide`). Vehicle: `CFC.sqrt`
(modern continuous-functional-calculus square root; `Matrix.PosSemidef.sqrt`
deprecated 2025-09-22). Content: existence/defining property, structure
(PSD/Hermitian), uniqueness, corollaries (√0, √1, √(A²)), determinant shadow,
concrete instance √diag(4,9) = diag(2,3).
