# Problem: Complete the Lean Formalization of Erdős #61 (Erdős–Hajnal Conjecture)

**Slug**: erdos-61-wip-01
**Created**: 2026-07-09T17:33:20-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall H,\; \exists c(H) > 0 \;:\; \forall G \text{ that is } H\text{-free},\; \max\big(\omega(G),\, \alpha(G)\big) \;\ge\; n^{\,c(H)}, \quad n = |V(G)|
$$

Here $H$-free means $G$ contains no induced copy of $H$, $\omega(G)$ is the clique number, and $\alpha(G)$ the independence number. This is the Erdős–Hajnal conjecture, which remains OPEN. The formalization goal is not to prove the conjecture but to faithfully state it in Lean 4, prove the routine structural lemmas around the clique/independence definitions, and cleanly isolate the genuinely-open core plus the known partial results as clearly-labelled assumptions.

### Plain Language

The Erdős–Hajnal conjecture says that if a graph avoids some fixed small pattern as an induced subgraph, then it must contain either a very large clique (all-connected group) or a very large independent set (all-disconnected group) — polynomially large, far bigger than ordinary Ramsey theory guarantees. This conjecture is famously unsolved. This project completes and hardens the existing Lean formalization: we do not attempt to settle the conjecture, but we make the Lean file a precise, auditable statement, prove the easy supporting facts from Mathlib, and mark the deep partial results and the open core as explicit assumptions.

### Why This Matters

1. **Central Open Problem**: Erdős–Hajnal is one of the most important unsolved questions in structural graph theory, connecting Ramsey theory to hereditary graph classes.
2. **Polynomial-vs-Logarithmic Gap**: It asks whether forbidding a pattern boosts the guaranteed clique/independent set from Ramsey's $\log n$ up to a polynomial $n^{c(H)}$.
3. **Auditable Formalization**: A faithful Lean statement, with the open core and 2023 partial bounds isolated as named assumptions, prevents overclaiming while giving a machine-checkable target for future work.

## Known Results

### What's Already Proven

- Erdős–Hajnal (1989): every $H$-free graph has a clique or independent set of size $\exp\big(c\sqrt{\log n}\big)$ — stated in the gallery Lean file as an axiom.
- Bucić–Nguyen–Scott–Seymour and related 2023 work: improved bounds of the form $\exp\big(c\sqrt{\log n \cdot \log\log n}\big)$ — stated as an axiom.
- The conjecture is proven for specific small $H$ (e.g. paths, and by Chudnovsky–Safra for certain configurations).
- Basic Lean definitions (the Erdős–Hajnal lower-bound property, the main conjecture as a `Prop`, concrete example graphs like the triangle and 3-path) already type-check with 0 sorries.

### What's Still Open

- The main conjecture itself: does a polynomial bound $n^{c(H)}$ hold for every fixed $H$?
- The optimal exponent $c(H)$ for specific graphs such as the 5-cycle.
- Whether a single uniform $c$ works for all $H$ on $k$ vertices, and whether the general bound can be pushed past $\exp\big(c\sqrt{\log n \cdot \log\log n}\big)$.

### Our Goal

Strengthen `Proofs/Erdos61Problem.lean` toward a maximally-honest state by (1) proving the routine relationships between `SimpleGraph.cliqueNum`, `SimpleGraph.indepNum`, and the induced-subgraph-free predicate from Mathlib, (2) verifying the concrete example graphs satisfy their claimed properties by decidable computation, and (3) reducing the axiom surface to exactly the open conjecture plus the two partial-result bounds, each documented precisely in `meta.json`. We must NOT claim to resolve the conjecture.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-61 | Parent gallery entry being completed | SimpleGraph clique/independence numbers, induced-subgraph-free predicates, Filter.Eventually |
| erdos-64 | Sibling open extremal-graph-theory entry with similar Lean scaffolding | SimpleGraph structure, minimum-degree and subgraph predicates, axiomatized deep results |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge the definitional and example lemmas.
   - Why it might work: relationships like $\max(\omega, \alpha) \ge 1$ for nonempty graphs, and the triangle and 3-path examples, follow from Mathlib's clique API and, for small graphs, `decide`.
   - Risk: `SimpleGraph.cliqueNum` and `indepNum` have subtle nonemptiness and finiteness side conditions that must be threaded carefully.

2. **Approach B**: Bundle the deep results into an `ErdosHajnalAxioms` structure.
   - Why it might work: collecting the 1989 and 2023 bounds and the open conjecture as fields makes the assumption inventory explicit and keeps the main statement readable.
   - Risk: per the Axiom Integrity Policy, structure fields are still assumptions and must be counted in `axiomCount`; this reorganizes but does not reduce the mathematical debt.

### Key Difficulties

- The conjecture is open, so its core cannot be discharged; the work is entirely about faithful statement and routine scaffolding.
- Encoding "induced $H$-free" correctly in Mathlib (induced subgraph embeddings versus arbitrary subgraphs) is error-prone and central to correctness.

### What Would a Proof Need?

- Key lemma 1: correct Mathlib encoding of induced-subgraph-freeness for a fixed $H$.
- Key lemma 2: decidable verification that the concrete example graphs have the stated clique and independence numbers.
- Technical requirements: careful use of `Filter.Eventually` for the "for large $n$" quantifier and honest axiom accounting.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematical core is a major open conjecture, so only faithful statement plus routine lemmas are achievable — the deep content stays axiomatized.
- Even the routine scaffolding requires careful handling of Mathlib's induced-subgraph and clique/independence APIs, which are nontrivial.
- Mathlib supplies `SimpleGraph.cliqueNum`, `indepNum`, and induced-subgraph machinery, but combining them faithfully is delicate.

**Estimated Effort**:
- Exploration: two to three days to map the encoding and axiom surface.
- If tractable: one to two weeks to discharge scaffolding lemmas and verify examples.
- If hard: the conjecture core remains open and axiomatized indefinitely.

## References

### Papers
- Erdős, Hajnal, "Ramsey-type theorems," Discrete Applied Mathematics, 1989 — origin of the conjecture and the $\exp(c\sqrt{\log n})$ bound.
- Bucić, Nguyen, Scott, Seymour, "Induced subgraph density," 2023 — improved partial bounds of the form $\exp\big(c\sqrt{\log n \cdot \log\log n}\big)$.

### Online Resources
- https://erdosproblems.com/61 — canonical statement and open status of Erdős Problem #61.

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Basic — `SimpleGraph` adjacency structure for encoding $G$ and $H$.
- Mathlib.Combinatorics.SimpleGraph.Clique — `SimpleGraph.cliqueNum` and `SimpleGraph.indepNum` for $\omega(G)$ and $\alpha(G)$.
- Mathlib.Order.Filter.Basic — `Filter.Eventually` for the asymptotic "for large $n$" quantifier.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - ramsey-theory
  - induced-subgraph
  - conjecture
  - formalization
  - structural-graph-theory
related_proofs:
  - erdos-61
  - erdos-64
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:20-07:00
```

**Significance**: 8/10
**Tractability**: 5/10
