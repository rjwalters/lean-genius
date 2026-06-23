# Problem: Erdős #268 — Complete the Path-Connectedness Sorry

**Slug**: erdos-268-incomplete-01
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The gallery proof `Proofs/Erdos268Problem.lean` establishes that $X_d$ (the set of $d$-tuples of harmonic subseries sums) has non-empty interior, but line 811 contains:

```lean
-- d ≥ 2: path-connectedness requires controlling d+2 coordinate sums simultaneously.
-- Kovač-Tao 2024 provides the mathematical foundation but Lean infrastructure is missing.
sorry
```

### Plain Language

Erdős #268: Can every point in a neighborhood of some $d$-tuple be expressed as a $d$-tuple of harmonic subseries sums? The $d=1$ case is handled, but the path-connectedness argument for $d \geq 2$ is a sorry.

### Why This Matters

Closes the last gap in the gallery's Erdős #268 formalization. The result is known (Kovač-Tao 2024) but the Lean proof infrastructure for multi-coordinate path control is missing.

## Known Results

### What's Already Proven
- $d=1$: complete in gallery
- Interior non-emptiness (uses the sorry transitively)
- Kovač (2024): Full characterization of $X_d$

### Our Goal

Fill the sorry at line 811 — either prove path-connectedness for $d \geq 2$, or restructure the proof to bypass it and directly exhibit an open ball in `harmonicPointSet d`.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-268` | Parent proof with sorry at line 811 |

## Initial Thoughts

### Potential Approaches

1. **Reformulate to avoid path-connectedness**: Directly exhibit an open ball in `harmonicPointSet d` by showing the map `A ↦ harmonicPoint A` is open near a specific `A`. Avoids multi-coordinate path control entirely.

2. **Direct construction for d=2**: Show two independent harmonic subseries can be varied independently to trace a 2D neighborhood.

### Key Difficulties
- Controlling multiple coordinate sums simultaneously while varying A ⊆ ℕ
- Lean's multi-dimensional topology API

## Tractability Assessment

**Difficulty**: Medium-High

- Mathematical result is settled (Kovač-Tao 2024)
- Gap is Lean infrastructure; restructuring may be achievable

## Metadata

```yaml
tags:
  - erdos
  - analysis
  - topology
  - harmonic-series
  - sorry-completion
  - seeker-selected
related_proofs:
  - erdos-268
difficulty: medium-high
source: gallery-gap
created: 2026-04-23
```

**Significance**: 7/10
**Tractability**: 6/10
