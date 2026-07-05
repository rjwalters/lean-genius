# Problem: Orthogonal determinant det O = ±1 for OᵀO = 1 over ℝ

**Slug**: det-conjugate-transpose-oq-01-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
O^{\mathsf T} O = I \ \Longrightarrow \ \det O = \pm 1 \qquad (O \in M_n(\mathbb{R})).
$$

### Plain Language

The parent entry `det-conjugate-transpose-oq-01` establishes the complex/unitary
statement about the conjugate transpose. This open question asks for the analogous
**real orthogonal** statement: an orthogonal matrix (one satisfying `Oᵀ O = I`) has
determinant `±1`. Both signs are realized (rotations give `+1`, reflections `−1`).

### Why This Matters

It is the real-field companion to the unitary determinant fact, closing the
orthogonal/unitary pair. It is the determinant-`±1` fact underlying the split of
`O(n)` into `SO(n)` and its reflection coset.

## Known Results

### What's Already Proven

- Parent `det-conjugate-transpose-oq-01`: determinant of the conjugate transpose /
  unitary case.
- Mathlib: `Matrix.det_transpose`, `Matrix.det_mul`, `Matrix.det_one`, and the
  `Matrix.orthogonalGroup` API.

### Our Goal

Prove `det O = 1 ∨ det O = -1` from `Oᵀ O = 1` over `ℝ`, and exhibit both signs.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| det-conjugate-transpose-oq-01 | parent; unitary analogue | determinant multiplicativity |

## Initial Thoughts

### Potential Approaches

1. **Determinant multiplicativity**: `det(Oᵀ O) = det Oᵀ · det O = (det O)² = det I = 1`,
   so `(det O)² = 1`, hence `det O = ±1` via `sq_eq_one_iff_of_ne_neg_one` / `mul_self_eq_one_iff`.
   - Why it might work: entirely in Mathlib; `det_transpose` gives `det Oᵀ = det O`.
   - Risk: minimal.

### What Would a Proof Need?

- `Matrix.det_transpose`, `Matrix.det_mul`, `mul_self_eq_one_iff` over `ℝ`.

## Tractability Assessment

**Difficulty**: Low

**Justification**: Direct from determinant multiplicativity; all ingredients are in
Mathlib. Bread-and-butter linear-algebra OQ-extension.

## References

### Mathlib
- `Mathlib.LinearAlgebra.Matrix.Orthogonal` / `Matrix.det_transpose`, `Matrix.det_mul`.

## Metadata

```yaml
tags:
  - linear-algebra
  - matrix
  - determinant
  - orthogonal
related_proofs:
  - det-conjugate-transpose-oq-01
difficulty: low
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 8/10
