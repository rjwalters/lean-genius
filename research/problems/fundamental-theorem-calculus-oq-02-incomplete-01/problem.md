# Problem: Generalized Stokes Theorem

**Slug**: fundamental-theorem-calculus-oq-02-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\int_{\partial M} \omega = \int_M d\omega
$$

### Plain Language

Formalize that FTC and Green's theorem are cases of Stokes theorem for differential forms. The framework is in place; 1 sorry blocks the full general statement.

### Why This Matters

See `src/data/proofs/fundamental-theorem-calculus-oq-02/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `fundamental-theorem-calculus-oq-02` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

Open question: bridge Mathlib's ContDiff.isSymmetric_iteratedFDeriv to concrete partial derivative expressions. May need SmoothManifoldWithCorners and ExteriorAlgebra.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `fundamental-theorem-calculus-oq-02` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - analysis
  - topology
  - stokes
  - differential-forms
  - manifolds
related_proofs:
  - fundamental-theorem-calculus-oq-02
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 8/10
**Tractability**: 5/10
