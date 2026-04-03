# Problem: Erdős #604: Pinned Distance Problem — Complete Proof

**Slug**: erdos-604-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \geq 2,\ \exists A \subset \mathbb{R}^2,\ |A| = n,\ \forall x \in A,\ |\{d(x,y) : y \in A\}| \leq \frac{n}{\sqrt{\log n}}
$$

### Plain Language

Given n distinct points in the plane, must some point have nearly n distinct distances to other points? The 'pinned' version of the distinct distances problem. OPEN with $500 prize.

The formalization has 1 sorry: `integerLattice_pinnedDistances` — the integer lattice achieves the conjectured upper bound construction (≤ n/√(log n) pinned distances per point).

### Why This Matters

The Erdős distinct distances problem is one of combinatorial geometry's most famous. The pinned version asks about a single point's distances. The integer lattice is the conjectured extremal construction.

## Known Results

### What's Already Proven

- `maxPinnedDistances` — sorry-free
- `pinnedDistance_le` — sorry-free
- Infrastructure for point sets and distance counting is complete

### Our Goal

Prove `integerLattice_pinnedDistances (n : ℕ) (hn : n ≥ 2)`:
- Construct A = first n points from integer lattice
- Show each x ∈ A has ≤ n/√(log n) distinct distances to other points
- This is a constructive existence proof

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-604` | Direct parent — inspect `Erdos604Problem.lean` line 182 |

## Initial Thoughts

### Potential Approaches

1. **Explicit integer lattice construction**: The key insight is that distances from a lattice point are sums of squares — circle method shows there are ≤ n/√(log n) distinct distances via Landau-Ramanujan theorem.
   - Requires: Landau-Ramanujan theorem (integers representable as sums of 2 squares)
   - Risk: Deep number theory — may not be in Mathlib

2. **Axiomatic supporting lemma**: Introduce a Mathlib-compatible axiom for the lattice distance count bound.
   - Risk: Reduces mathematical contribution

### Key Difficulties

- The bound n/√(log n) on distinct distances from a lattice point requires the Landau-Ramanujan theorem
- May not be available in Mathlib; deep analytic number theory

### What Would a Proof Need?

- Landau-Ramanujan theorem or weaker Mathlib-available bound
- Integer lattice point set definition as `Finset (ℤ × ℤ)`
- `Finset.card` bounds on distance sets

## Tractability Assessment

**Difficulty**: Hard

**Justification**:
- The sorry is for a result requiring Landau-Ramanujan theorem
- This is an open research problem with $500 prize
- Constructive upper bound for extremal configuration requires deep analytic number theory

## Metadata

```yaml
tags:
  - erdos
  - discrete-geometry
  - distinct-distances
  - combinatorial-geometry
  - open-problem
  - lattice
related_proofs:
  - erdos-604
difficulty: hard
source: gallery-gap
created: 2026-04-03
```

**Significance**: 7/10
**Tractability**: 4/10
