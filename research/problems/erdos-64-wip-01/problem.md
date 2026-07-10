# Problem: Complete the Lean Formalization of Erdős #64 (Power-of-Two Cycles in Min-Degree-3 Graphs)

**Slug**: erdos-64-wip-01
**Created**: 2026-07-09T17:33:20-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall G \text{ finite},\; \delta(G) \ge 3 \;\Longrightarrow\; \exists k \ge 2 \;:\; C_{2^k} \subseteq G
$$

Here $\delta(G)$ is the minimum degree and $C_{2^k}$ is the cycle of length $2^k$. The Erdős–Gyárfás conjecture asserts that every finite graph with minimum degree at least $3$ contains a cycle whose length is a power of two. It carries a \$1000 prize and remains OPEN at $\delta = 3$. The formalization goal is to faithfully state this in Lean 4, prove the routine graph-theoretic scaffolding, and isolate the deep open core (and the Liu–Montgomery large-degree resolution) as clearly-labelled assumptions.

### Plain Language

The Erdős–Gyárfás conjecture asks whether every finite graph in which every vertex has at least three neighbours must contain a cycle whose length is a power of two (4, 8, 16, 32, and so on). Although powers of two are exponentially sparse, they are conjectured to be unavoidable under this mild degree condition. The problem is famously open at minimum degree exactly three and carries a \$1000 Erdős prize. This project completes and hardens the existing Lean formalization: we do not attempt to settle the conjecture, but we make the statement precise, prove the routine cycle-and-degree lemmas, and mark the deep results as explicit assumptions.

### Why This Matters

1. **Prize Open Problem**: Erdős–Gyárfás is a prominent \$1000-prize question in extremal graph theory, with all the difficulty concentrated at minimum degree three.
2. **Sparse Unavoidable Sets**: It probes when an exponentially sparse set of cycle lengths becomes unavoidable, sharpening our understanding of pancyclicity-type phenomena.
3. **Honest Formalization**: A faithful Lean statement, isolating the open core and the Liu–Montgomery large-degree theorem as named assumptions, keeps the gallery entry credible and gives a machine-checkable target.

## Known Results

### What's Already Proven

- Liu–Montgomery (2020): there is a threshold $D$ such that every graph with $\delta(G) \ge D$ contains all even cycle lengths in a geometric range, hence a power-of-two cycle — stated in the gallery Lean file as an axiom.
- The Erdős–Gyárfás counter-conjecture (that sparse graphs avoid such cycles) was disproved, and the infinite $3$-regular tree shows finiteness is essential — captured in the source.
- Classical supporting results: Dirac's Hamiltonicity theorem, Bondy's pancyclicity, and random-graph cycle-length facts.
- Basic Lean definitions (cycle containment $C_{2^k}$ via cyclic adjacency, minimum degree via `Finset.inf'`, the powers-of-two set, the main conjecture as a `Prop`) already type-check with 0 sorries.

### What's Still Open

- The conjecture at minimum degree exactly three — the entire remaining difficulty (\$1000 prize).
- The exact Liu–Montgomery threshold $D$ and whether it can be reduced to a small constant.
- Whether the result extends to other sparse target sequences (Fibonacci numbers, primes) as unavoidable cycle lengths.

### Our Goal

Strengthen `Proofs/Erdos64Problem.lean` toward a maximally-honest state by (1) proving from Mathlib the routine facts about `neighborFinset`, minimum degree via `Finset.inf'`, and cyclic adjacency via `Fin.succMod`, (2) verifying that the cycle-containment predicate for $C_{2^k}$ correctly encodes an actual cycle subgraph, and (3) reducing the axiom surface to the open conjecture plus the Liu–Montgomery theorem, documenting each assumption precisely in `meta.json`. We must NOT claim to resolve the conjecture.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-64 | Parent gallery entry being completed | SimpleGraph cycle containment, minimum degree via Finset.inf', cyclic adjacency Fin.succMod |
| erdos-85 | Sibling extremal-graph-theory entry on minimum degree forcing a small cycle | SimpleGraph.minDegree, cycle-forcing thresholds, asymptotic axioms |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge the degree and cyclic-adjacency lemmas.
   - Why it might work: minimum degree via `Finset.inf'` over `neighborFinset` cardinalities, and cyclic adjacency via `Fin.succMod`, are supported by Mathlib's `Finset` and `Fin` APIs and need no new mathematics.
   - Risk: `Finset.inf'` requires nonemptiness proofs, and cycle-subgraph encoding via `Fin (2^k)` indexing can be fiddly to relate to genuine cycle containment.

2. **Approach B**: Bundle the deep results into an `Erdos64Axioms` structure.
   - Why it might work: collecting the open conjecture and the Liu–Montgomery theorem as fields makes the assumption inventory explicit and keeps the main statement readable.
   - Risk: per the Axiom Integrity Policy, structure fields remain assumptions and must be counted in `axiomCount`; this reorganizes but does not reduce the debt.

### Key Difficulties

- The conjecture is open at $\delta = 3$, so its core cannot be discharged; work is limited to faithful statement and routine scaffolding.
- Faithfully encoding "$C_{2^k} \subseteq G$" as an injective cyclic walk (not merely a closed walk with repeats) is the central correctness subtlety.

### What Would a Proof Need?

- Key lemma 1: correct definition and basic properties of minimum degree via `Finset.inf'` over `neighborFinset`.
- Key lemma 2: a faithful cycle-containment predicate for $C_{2^k}$ using `Fin.succMod` cyclic adjacency with injectivity.
- Technical requirements: nonemptiness side conditions for `Finset.inf'`, and honest axiom accounting for the open core.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematical core is a \$1000-prize open problem, so only faithful statement plus routine lemmas are achievable — the deep content stays axiomatized.
- The routine scaffolding (minimum degree, cyclic adjacency, cycle containment) is within Mathlib's reach but requires careful nonemptiness and injectivity handling.
- Mathlib provides `neighborFinset`, `Finset.inf'`, and `Fin.succMod`, covering the mechanical parts.

**Estimated Effort**:
- Exploration: two to three days to map the encoding and axiom surface.
- If tractable: one to two weeks to discharge scaffolding lemmas and verify the cycle predicate.
- If hard: the conjecture core remains open and axiomatized indefinitely.

## References

### Papers
- Liu, Montgomery, "A solution to Erdős and Hajnal's odd cycle problem," and related even-cycle work, 2020 — resolves the large-minimum-degree case.
- Erdős, Gyárfás, "A variant of the classical Ramsey problem," Combinatorica, 1997 — origin of the power-of-two cycle conjecture and counter-conjecture.

### Online Resources
- https://erdosproblems.com/64 — canonical statement and open status of Erdős Problem #64.

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Basic — `SimpleGraph` and `neighborFinset` for encoding $G$ and degrees.
- Mathlib.Data.Finset.Lattice — `Finset.inf'` for minimum degree over nonempty vertex sets.
- Mathlib.Data.Fin.Basic — `Fin.succMod` for cyclic adjacency used in the cycle-containment predicate.

## Metadata

```yaml
tags:
  - erdos
  - extremal-graph-theory
  - cycles
  - minimum-degree
  - graph-theory
  - formalization
  - open-problem
related_proofs:
  - erdos-64
  - erdos-85
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:20-07:00
```

**Significance**: 8/10
**Tractability**: 5/10
