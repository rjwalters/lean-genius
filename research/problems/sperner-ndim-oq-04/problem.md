# Problem: n-Dimensional Sperner: Kuhn Path-Following Algorithm Formalization

## Statement

### Plain Language
Formalize Kuhn's (1968) constructive proof of Sperner's lemma via path-following in the door adjacency graph of an abstract triangulation. Starting from a boundary door, follow the unique path to reach a fully-colored simplex.

### Formal Statement
For a Sperner-colored abstract triangulation satisfying the Kuhn compatibility axiom (door degree ≤ 2), the path-following algorithm starting from a boundary door terminates at a fully-colored simplex.

## Classification

```yaml
tier: A
significance: 8
tractability: 6
tags:
  - combinatorics
  - algorithms
  - sperner
  - kuhn
  - constructive
```

**Significance**: 8/10 — Kuhn's algorithm is the foundation of fixed-point computation methods (Lemke-Howson, Scarf)
**Tractability**: 6/10 — Core lemmas proved; non-revisiting invariant remains

## Why This Matters

1. **Constructive proof** — Unlike parity arguments, Kuhn's algorithm gives an explicit path to the FC simplex
2. **Algorithm foundation** — Basis for Lemke-Howson algorithm for Nash equilibria and Scarf's fixed-point method
3. **Formal verification** — Demonstrates that door graph path-following can be machine-checked in Lean 4

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| sperner-ndim | Core infrastructure: SpernerTriangulation, abstract_door_parity, door_transfer |
| sperner-ndim-oq-01 | Freudenthal triangulation likely satisfies IsKuhnCompatible |
| sperner-ndim-oq-03 | Displacement coloring uses similar door structure for Brouwer FPT |
