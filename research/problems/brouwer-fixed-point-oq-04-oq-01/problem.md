# Problem: Nash equilibrium existence for finite games via the Kakutani fixed point theorem

**Slug**: brouwer-fixed-point-oq-04-oq-01
**Created**: 2026-04-02T21:57:15-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For every finite N-player normal-form game `G` with `N > 0`, there exists a
mixed-strategy profile that is a fixed point of the joint best-response
correspondence — a Nash equilibrium. Formalized as `nash_existence` in
`proofs/Proofs/BrouwerFixedPointOQ04OQ01.lean`, modulo two stated axioms:

- `bestResponse_uhc` — upper hemicontinuity of the best-response
  correspondence (Berge maximum theorem).
- `kakutani_product_simplex` — Kakutani fixed point theorem on the product
  simplex.

### Plain Language

Prove that every finite normal-form game has at least one Nash equilibrium in
mixed strategies, using the Kakutani fixed point theorem. The Lean development
defines expected utility and the best-response correspondence (proved nonempty,
convex, and closed), then derives Nash existence from a Kakutani fixed point of
the joint best response.

### Why This Matters

- Nash existence is the foundational theorem of non-cooperative game theory
  (Nash 1950).
- It connects a Brouwer/Kakutani fixed-point development to a set-valued
  (correspondence) fixed point application inside Lean.
- The two remaining axioms (Berge maximum theorem, Kakutani) are not yet in
  Mathlib, so this entry also scopes concrete Mathlib gaps.

## Known Results

### What's Already Proven (in this repo)

- `proofs/Proofs/BrouwerFixedPointOQ04OQ01.lean` (297 lines, 8 theorems, 2
  axioms, 0 sorries): expected-utility/best-response framework, with the
  best-response correspondence proved nonempty (`bestResponse_nonempty`),
  convex (`bestResponse_convex`), and closed (`bestResponse_closed`), and
  `nash_existence` derived from the two axioms.

### What's Still Open

- Discharge `bestResponse_uhc` (Berge maximum theorem).
- Discharge `kakutani_product_simplex` (Kakutani fixed point theorem).

### Our Goal

Reduce the two stated axioms to theorems. Both are large upstream-Mathlib
foundations rather than gallery-sized work — see `state.md` for the live
upstream-tracking analysis and `knowledge.md` for the dependency map.

## Tractability Assessment

**Difficulty**: High (blocked on upstream Mathlib foundations)

**Justification**:
- Berge's maximum theorem is estimated at ~300–500 LOC of Mathlib-style work.
- Kakutani's fixed point theorem is estimated at ~500–1500 LOC and has no
  Mathlib activity at head-of-tree.
- The pinned Mathlib (v4.26.0) lacks an upper-hemicontinuity predicate API;
  the UHC API merged to Mathlib head-of-tree on 2026-01-09 (PR #33626) but is
  not in the pin.

## References

### Papers
- Nash, J. (1950), "Equilibrium points in n-person games", PNAS.
- Berge, C. (1963), *Topological Spaces* (maximum theorem).
- Kakutani, S. (1941), "A generalization of Brouwer's fixed point theorem".

### Mathlib
- `Mathlib.Topology.*`, `Mathlib.Analysis.Convex.*` — used for the
  best-response framework. Missing: UHC predicate API (in head-of-tree),
  Berge maximum theorem, Kakutani fixed point theorem.

## Metadata

```yaml
tags:
  - game-theory
  - topology
  - fixed-point
related_proofs:
  - brouwer-fixed-point
difficulty: high
source: user-request
created: 2026-04-02T21:57:15-07:00
```

**Significance**: 8/10
**Tractability**: 3/10
