# Problem: Erdős #268 — Complete the Path-Connectedness Sorry

**Slug**: erdos-268-incomplete-01
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The gallery proof `Proofs/Erdos268Problem.lean` establishes that $X_d$ (the set of $d$-tuples
of harmonic subseries sums) has non-empty interior, but line 811 contains:

```lean
-- d ≥ 2: path-connectedness requires controlling d+2 coordinate sums simultaneously.
-- Kovač-Tao 2024 provides the mathematical foundation but Lean infrastructure is missing.
sorry
```

**Goal**: Fill the sorry at line 811, establishing path-connectedness of the interior of
`harmonicPointSet d` for d ≥ 2.

### Plain Language

Erdős #268 asks: can every point in a neighborhood of some $d$-tuple $(s_1, \ldots, s_d)$ be
expressed as a $d$-tuple of harmonic subseries sums? The $d = 1$ case is handled, but the
path-connectedness argument for $d \geq 2$ — needed to show the interior is connected —
currently rests on a sorry.

### Why This Matters

Closes the last gap in the gallery's Erdős #268 formalization. Kovač (2024) established the
full characterization of $X_d$ in the literature; the Lean proof infrastructure for
multi-coordinate path control is all that's missing.

## Known Results

### What's Already Proven

- $d = 1$: complete in gallery (`erdos-268`)
- Non-emptiness of interior: proven (uses the sorry transitively)
- Kovač (2024): Full characterization of $X_d$ in Annals

### What's Still Open

- Path-connectedness argument for $d \geq 2$ in Lean

### Our Goal

Fill the sorry at line 811 of `proofs/Proofs/Erdos268Problem.lean`. Either:
1. Prove path-connectedness for $d \geq 2$ directly, or
2. Restructure to bypass path-connectedness by directly exhibiting an open ball.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-268` | Parent proof with the sorry at line 811 | Harmonic subseries, set interior |

## Initial Thoughts

### Potential Approaches

1. **Reformulate to avoid path-connectedness**: Directly exhibit an open ball in
   `harmonicPointSet d` by showing the map `A ↦ harmonicPoint A` is open near a specific
   multi-index `A`. Uses the inverse function theorem or openness of projection.
   - Why it might work: avoids multi-coordinate path control entirely
   - Risk: IFT in Lean over arbitrary countable index sets may be difficult

2. **Direct path construction**: Given two points in the interior, construct a continuous
   path via linear interpolation of harmonic sum indices, using the stability lemma.
   - Why it might work: Kovač's explicit construction is available in the paper
   - Risk: Lean formalization of the continuity argument for $d+2$ coordinate sums simultaneously

3. **Local convexity**: Show the set is locally convex near the Kovač center, making
   path-connectedness trivial in a neighborhood.
   - Why it might work: convexity is easier than general path-connectedness in Mathlib
   - Risk: requires showing the map is a local diffeomorphism

### Key Difficulties

- Multi-coordinate harmonic sum control: fixing $d+2$ partial sums simultaneously
- Lean path-connectedness infrastructure in `Topology.IsPathConnected`

### What Would a Proof Need?

- Key lemma: The harmonic point map is locally surjective near the Kovač center
- Technical requirement: `IsPathConnected.mem_pathComponent` or similar Mathlib tooling
- Alternative: `IsOpen.isPathConnected_of_isConnected` if connectedness is easier to show

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is settled (Kovač 2024)
- The sorry is a well-scoped gap in Lean infrastructure
- Alternative proof routes (local convexity, open ball exhibit) may sidestep the hard part
- Similar "complete a known result" tasks have succeeded in 1-3 sessions

**Estimated Effort**:
- Exploration: 1-2 sessions (read the Lean file, understand what's needed)
- If tractable: 2-4 sessions
- If hard: restructure proof to avoid path-connectedness

## References

### Papers
- Kovač, V. (2024). "On the harmonic series point sets" — Annals. Full characterization of X_d.

### Mathlib
- `Topology.IsPathConnected` — path-connectedness API
- `Analysis.SpecificLimits.Basic` — harmonic series lemmas
- `Topology.MetricSpace.Basic` — metric space openness tools

## Metadata

```yaml
tags:
  - number-theory
  - harmonic-analysis
  - erdos-problem
  - completion
related_proofs:
  - erdos-268
difficulty: medium
source: gallery-gap
created: 2026-04-23
```
