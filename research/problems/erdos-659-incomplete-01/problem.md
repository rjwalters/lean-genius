# Problem: Erdős Problem #659: Point Configurations with Few Distances

**Slug**: erdos-659-incomplete-01
**Created**: 2026-04-03T05:22:49
**Updated**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The problem is sourced from the gallery proof `erdos-659`.

**Gallery proof status**: 1 sorry(s), 1 axiom(s)

**Problem Type**: COMPLETION

### Open Question

Complete the formalization of Erdős Problem #659: Point Configurations with Few Distances by resolving 1 sorry statement(s)

### Plain Language

Is there a set of n points in R² such that every 4-point subset determines at least 3 distances, yet the total distinct distances is O(n/√log n)? Answer: Yes, via the Moree-Osburn lattice.

## Gallery Context

- **Gallery Entry**: `erdos-659`
- **Title**: Erdős Problem #659: Point Configurations with Few Distances
- **Tags**: erdos, combinatorial-geometry, distance-problems, lattices
- **Sorries**: 1
- **Axioms**: 1

## Mathematical Background

See gallery entry for mathematical background.

## Research Approach

### For OBSERVE Phase
1. Read the gallery proof at `src/data/proofs/erdos-659/meta.json`
2. Study the Lean source file
3. Understand existing proof structure and the sorry statement(s)

### For ORIENT Phase
4. Research relevant Mathlib tactics and lemmas
5. Check for related gallery proofs

### For DECIDE Phase
6. Design a proof strategy

### For ACT Phase
7. Implement the proof
8. Verify with docker-build.sh

## Significance: 7/10
## Tractability: 6/10 (challenging)
