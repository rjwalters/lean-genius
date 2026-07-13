# Problem: Complete Erdős Problem #1068 — Countable Infinitely-Connected Subgraphs

**Slug**: erdos-1068-wip-01
**Created**: 2026-07-09T19:15:59-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\, G\ \big(\chi(G) = \aleph_1\big) \ \Longrightarrow\ \exists\, H \subseteq G\ \text{countable with}\ H\ \text{infinitely vertex-connected}.
$$

**Question:** does every graph of chromatic number $\aleph_1$ contain a *countable* subgraph that is infinitely (vertex-)connected?

### Plain Language

Colour the vertices of a graph so adjacent vertices differ; suppose you genuinely need uncountably many ($\aleph_1$) colours. Must the graph then contain a small (countable) piece that is extremely well-connected — one that stays connected after deleting any finite set of vertices? This is a countable-subgraph refinement of the Erdős–Hajnal program relating chromatic number to connectivity.

### Why This Matters

It is part of the **Erdős–Hajnal** structural program (1966) linking large chromatic number to forced substructure. Soukup (2015, *Combinatorica*) constructed, in ZFC, an uncountably chromatic graph where every *uncountable* vertex set fails high connectivity — showing the naive uncountable version is false and sharpening attention on the *countable* formulation, which remains open.

## Known Results

### What's Already Proven

- **Erdős–Hajnal (1966):** foundational results connecting chromatic number and set-system structure.
- **Soukup (2015):** first ZFC construction of an uncountably chromatic graph in which every uncountable set is at most finitely connected — refutes the uncountable analogue.
- Classical infinite-graph connectivity theory (Menger's theorem for infinite graphs).
- Gallery entry `erdos-1068` formalizes the chromatic-number / connectivity framing in Lean.

### What's Still Open

- The countable-subgraph version (the main question) is open.
- Whether the answer is independent of ZFC / sensitive to additional set-theoretic axioms.

### Our Goal

Complete the WIP gallery formalization `erdos-1068`: formalize chromatic number $\aleph_1$, the notion of infinite vertex-connectivity, and the precise conjecture as a formal proposition. Formalize what is settled (e.g. Soukup's obstruction at the uncountable level, or reductions), discharging remaining scaffolding.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1068 | Base WIP entry this problem completes | infinite chromatic number, connectivity |
| — | Menger-type infinite-graph connectivity | set theory / graph theory |

## Initial Thoughts

### Potential Approaches

1. **Formalize the definitions and statement precisely**: chromatic number as a cardinal, $k$-vertex-connectivity, and the $\aleph_1 \Rightarrow$ countable-infinitely-connected implication.
   - Why it might work: getting the statement type-correct in Mathlib is a concrete, valuable deliverable even without a full proof.
   - Risk: Mathlib's `SimpleGraph` cardinal-chromatic and infinite-connectivity support is thin; may need new definitions.

2. **Formalize the Soukup obstruction / uncountable counterexample framing**: state why the uncountable analogue fails, isolating what makes the countable version subtle.
   - Why it might work: clarifies the problem boundary and records a genuine theorem.
   - Risk: the full ZFC construction is intricate to formalize.

### Key Difficulties

- Infinite/cardinal chromatic number and infinite connectivity are under-developed in Mathlib.
- The core question is open and possibly set-theoretically sensitive.

### What Would a Proof Need?

- Key lemma 1: a workable Lean definition of infinite vertex-connectivity for `SimpleGraph`.
- Key lemma 2: cardinal-valued chromatic number with $\chi(G) = \aleph_1$ expressible.
- Technical requirements: `Mathlib.Combinatorics.SimpleGraph`, `Mathlib.SetTheory.Cardinal`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The main question is an open Erdős–Hajnal-type problem, possibly independent of ZFC.
- Formalizing definitions and the statement is a realistic, useful completion target.
- Mathlib's infinite-graph / cardinal support is limited, so groundwork may be needed.

**Estimated Effort**:
- Exploration: days
- If tractable (definitions + statement + partial results): weeks
- If hard (full resolution): unknown

## References

### Papers
- P. Erdős, A. Hajnal, "On chromatic number of graphs and set-systems," *Acta Math. Acad. Sci. Hungar.* 17 (1966) 61–99.
- L. Soukup, construction of uncountably chromatic graphs with low connectivity, *Combinatorica* (2015).
- Menger's theorem for infinite graphs (Aharoni–Berger and classical sources).

### Online Resources
- Erdős Problems database, Problem #1068 — https://www.erdosproblems.com/1068

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Connectivity` — connectivity primitives.
- `Mathlib.SetTheory.Cardinal.Basic` — $\aleph_1$ and cardinal chromatic number.

## Metadata

```yaml
tags:
  - graph-theory
  - set-theory
  - chromatic-number
  - infinite-connectivity
related_proofs:
  - erdos-1068
difficulty: high
source: proof-suggestion
created: 2026-07-09T19:15:59-07:00
```
