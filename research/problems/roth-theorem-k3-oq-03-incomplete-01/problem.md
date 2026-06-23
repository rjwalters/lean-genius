# Problem: Density Increment via Gowers Norms

**Slug**: roth-theorem-k3-oq-03-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\|f\|_{U^3} \geq \delta \Rightarrow \exists \text{ density increment on progression}
$$

### Plain Language

Generalization of Roth density increment to k-APs using Gowers uniformity norms. Gowers norms and k-AP counting operator defined. 1 sorry + 2 axioms for the main estimate.

### Why This Matters

See `src/data/proofs/roth-theorem-k3-oq-03/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `roth-theorem-k3-oq-03` provides the foundation
- sorries to fill: 1 (plus any axioms — check source proof)

### Our Goal

For k=3, the density increment from U^2 norms follows from Roth infrastructure. Check if the existing RothTheorem.lean results can be directly applied via Fourier inversion.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `roth-theorem-k3-oq-03` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - combinatorics
  - gowers-norms
  - additive-combinatorics
  - density-increment
related_proofs:
  - roth-theorem-k3-oq-03
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 5/10
