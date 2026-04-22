# Problem: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

**Slug**: sperner-ndim-oq-04
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a Sperner-colored abstract triangulation satisfying the Kuhn compatibility axiom
(door degree ≤ 2), the path-following algorithm starting from a boundary door terminates
at a fully-colored simplex.

### Plain Language

Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the
door adjacency graph of an abstract triangulation. Starting from a boundary door, follow
the unique path to reach a fully-colored simplex. This is the algorithmic foundation for
fixed-point computation (Lemke-Howson for Nash equilibria, Scarf's method).

### Why This Matters

- **Constructive proof**: Unlike parity arguments, Kuhn's algorithm gives an explicit path
  to the fully-colored simplex
- **Algorithm foundation**: Basis for Lemke-Howson algorithm (Nash equilibria) and Scarf's
  fixed-point method
- **Active initiative**: Part of the Mathlib n-Dim Sperner project

## Current Lean Status

- **Lean file**: `proofs/Proofs/SpernerNDimOQ04.lean` (~290 lines, created 2026-04-22)
- **Gallery data**: `src/data/proofs/sperner-ndim-oq-04/` (meta.json, annotations.json, index.ts)
- **Phase**: ACT — 3 sorries remain for path termination

### Proven (Session 2026-04-22)

1. `fc_door_count_eq_one` — Under IsKuhnCompatible, FC simplices have exactly 1 door
2. `nonfc_door_count_zero_or_two` — Under IsKuhnCompatible, non-FC simplices have 0 or 2 doors
3. `nonfc_with_door_has_unique_exit` — Non-FC simplex with entry door has unique exit door

### Remaining Sorries (3)

1. `kuhn_path_terminates` — Main existence theorem (depends on non-revisiting invariant)
2. `kuhn_walk_reaches_fc` — Walk correctness (requires non-revisiting invariant)
3. `kuhnPathStart_is_fc` — Top-level correctness (depends on above two)

## Classification

```yaml
tier: A
significance: 8
tractability: 6
tags:
  - combinatorics
  - algorithms
  - topology
  - sperner
  - kuhn
  - constructive
```

**Significance**: 8/10 — Kuhn's algorithm is the foundation of fixed-point computation
**Tractability**: 6/10 — Core lemmas proved; non-revisiting invariant remains

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| sperner-ndim | Core infrastructure: SpernerTriangulation, abstract_door_parity, door_transfer |
| sperner-ndim-oq-01 | Freudenthal triangulation likely satisfies IsKuhnCompatible |
| sperner-ndim-oq-03 | Displacement coloring uses similar door structure for Brouwer FPT |
