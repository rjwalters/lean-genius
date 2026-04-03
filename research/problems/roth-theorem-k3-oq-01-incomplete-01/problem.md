# Problem: Roth's Theorem: Main k=3 Formalization

**Slug**: roth-theorem-k3-oq-01-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall \delta > 0, \exists N_0: \forall N \geq N_0, A \subset \mathbb{Z}_N, |A| \geq \delta N \Rightarrow A \text{ has 3-AP}
$$

### Plain Language

Main sorry-filling task for Roth's theorem. The Lean file has 5 sorries remaining. Mathlib corners chain provides the key building block.

### Why This Matters

See `src/data/proofs/roth-theorem-k3-oq-01/meta.json` for full context. This is a targeted completion/extension of an existing gallery proof.

## Known Results

### What's Already Proven

- Parent proof `roth-theorem-k3-oq-01` provides the foundation
- sorries to fill: 5 (plus any axioms — check source proof)

### Our Goal

Import from RothTheorem.lean (which uses Mathlib's corners theorem). The 5 sorries likely involve bridging between local definitions and Mathlib's Finset.addCornerFree. Start with OBSERVE phase to map all 5 sorries.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `roth-theorem-k3-oq-01` | Direct parent — inspect its Lean file for sorry locations |

## Tractability Assessment

**Difficulty**: Challenging

## Metadata

```yaml
tags:
  - combinatorics
  - roth
  - arithmetic-progressions
  - fourier
related_proofs:
  - roth-theorem-k3-oq-01
difficulty: challenging
source: gallery-gap
created: 2026-04-03
```

**Significance**: 8/10
**Tractability**: 4/10
