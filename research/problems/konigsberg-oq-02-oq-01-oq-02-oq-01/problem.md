# Problem: Hierholzer undirected sufficiency — even-degree connected graph has an Eulerian circuit

**Slug**: konigsberg-oq-02-oq-01-oq-02-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

**Euler's theorem, sufficiency (undirected).** Let $G$ be a finite connected (multi)graph in which every vertex has even degree. Then $G$ has an Eulerian circuit — a closed walk traversing every edge exactly once.

$$
G \text{ connected} \ \wedge\ (\forall v,\ \deg(v)\text{ even}) \ \Longrightarrow\ \exists\ \text{Eulerian circuit in } G.
$$

### Plain Language

The famous Königsberg-bridges result has an easy necessity direction (an Eulerian circuit forces all degrees even). This problem is the harder **sufficiency** direction via Hierholzer's algorithm: if a connected graph has all even degrees, you can actually build a single closed tour using every edge once by splicing together cycles.

### Why This Matters

The gallery has the Königsberg/necessity material, but the undirected sufficiency (converse) is noted as still open in the gallery. Formalizing Hierholzer's constructive argument closes the characterization and adds a classic algorithmic-combinatorics result.

## Known Results

### What's Already Proven

- Necessity direction and the Königsberg impossibility — parent proof `konigsberg-oq-02-oq-01-oq-02` (verified).
- Mathlib `SimpleGraph.Walk.IsEulerian`, `IsTrail`, `IsCircuit`, and degree API.
- The directed Eulerian characterization exists in Mathlib (`SimpleGraph`/`Digraph` Eulerian lemmas) and can guide the undirected proof.

### What's Still Open

- The undirected sufficiency direction in this repository (flagged open in the gallery).
- Whether to build on Mathlib's `IsEulerian` existence lemmas directly or reprove Hierholzer's splicing.

### Our Goal

Prove: a finite connected graph with all even degrees admits an Eulerian circuit, formalizing Hierholzer's cycle-splicing argument (or invoking/adapting Mathlib's Eulerian existence infrastructure), for the undirected case.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg-oq-02-oq-01-oq-02 | Parent: Königsberg / necessity direction (verified) | degree parity, walks |
| konigsberg-oq-01 | Original Königsberg formalization and graph setup | graph encoding |

## Initial Thoughts

### Potential Approaches

1. **Use Mathlib's Eulerian existence lemmas**: Check whether `SimpleGraph.Walk.IsEulerian` comes with an existence theorem under connectivity + even-degree hypotheses and adapt it.
   - Why it might work: if Mathlib already has the sufficiency lemma, this becomes an application + hypothesis matching.
   - Risk: Mathlib may only have the *necessity* direction or a directed version; must verify coverage.

2. **Formalize Hierholzer directly**: Induct on the number of edges; extract a cycle through a chosen vertex (possible since even degrees), remove it, apply induction to components, and splice cycles at shared vertices.
   - Why it might work: constructive and standard; connectivity guarantees splice points.
   - Risk: strong-induction bookkeeping, component connectivity after edge removal, and the splicing lemma are nontrivial in Lean.

### Key Difficulties

- Choosing the graph model (multigraph vs `SimpleGraph`) — Eulerian statements care about parallel edges.
- The cycle-extraction and splicing steps, and maintaining connectivity/even-degree invariants under edge removal.

### What Would a Proof Need?

- Key lemma 1: in a graph with all even (positive) degrees, every vertex lies on a cycle.
- Key lemma 2: splicing two edge-disjoint circuits sharing a vertex yields a circuit.
- Technical requirements: `Fintype` graph, `SimpleGraph.Walk` API, strong induction on edge count.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathematically classical, but Hierholzer's induction is one of the heavier finite-graph arguments to mechanize.
- Tractability improves substantially if Mathlib's `IsEulerian` existence lemma covers the undirected case (first thing to check).
- Parent provides the degree-parity and walk scaffolding.

**Estimated Effort**:
- Exploration: 1 day (survey Mathlib Eulerian coverage first)
- If tractable: 4–7 days
- If Mathlib lacks the existence lemma: potentially longer (full Hierholzer)

## References

### Papers
- Euler (1736), Seven Bridges of Königsberg.
- Hierholzer (1873), constructive existence of Eulerian circuits.

### Online Resources
- Wikipedia: "Eulerian path", "Hierholzer's algorithm".

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Trails` — `IsEulerian`, `IsTrail`, `IsCircuit`.
- `SimpleGraph.degree`, `SimpleGraph.Connected` — hypotheses and invariants.

## Metadata

```yaml
tags:
  - graph-theory
  - eulerian
  - hierholzer
  - konigsberg
related_proofs:
  - konigsberg-oq-02-oq-01-oq-02
  - konigsberg-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
