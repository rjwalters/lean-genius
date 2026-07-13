# Problem: Extending RamseyProp to Hypergraphs and Multicolorings

**Slug**: ramsey-r4k-oq-04
**Created**: 2026-07-04
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall\, r, k_1, \dots, k_c,\ \exists\, N,\ \text{such that every } c\text{-coloring of } \binom{[N]}{r} \text{ has a monochromatic } K_{k_i}^{(r)} \text{ in some color } i.
$$

Here $\binom{[N]}{r}$ is the set of $r$-subsets, and $K_k^{(r)}$ is the complete $r$-uniform hypergraph on $k$ vertices. This generalizes the graph case ($r=2$, $c=2$) captured by the existing `RamseyProp`.

### Plain Language

The gallery's `ramsey-r4k` entry defines a `RamseyProp` predicate for 2-colorings of edges of a graph. This open question asks to extend that definition — and the finiteness theorem — to (a) $r$-uniform hypergraphs (colorings of $r$-subsets) and (b) more than two colors (multicolorings). The core result is Ramsey's theorem in full generality: the hypergraph Ramsey number $R_r(k_1,\dots,k_c)$ is finite. As a stretch goal, this framework is the natural home for the Hales–Jewett theorem.

### Why This Matters

Ramsey's theorem for hypergraphs and multicolorings is a foundational result whose full-generality formalization is genuinely useful infrastructure — it underpins density and structural Ramsey theory. Extending an existing, tested `RamseyProp` definition is a concrete, well-scoped generalization with a clear inductive proof (Ramsey's original double induction on $r$ and the $k_i$).

## Known Results

### What's Already Proven

- Graph Ramsey theorem $R(s,t) < \infty$ and finiteness — Mathlib has `SimpleGraph` Ramsey material and the gallery parent `ramsey-r4k`.
- Ramsey's theorem for $r$-uniform hypergraphs (finiteness) — classical, Ramsey 1930; not fully in the gallery in general form.
- Erdős–Rado stepping-up and upper bounds for hypergraph Ramsey numbers — classical.

### What's Still Open

- A general-form Lean statement + proof of finiteness for arbitrary $r$ and $c$ colors, built on the existing `RamseyProp`.
- Hales–Jewett theorem (the stretch goal) — much harder, combinatorial-line machinery.

### Our Goal

Define `RamseyPropHyper r c k` extending `RamseyProp`, prove finiteness of the $c$-color $r$-uniform Ramsey number by the standard double induction, and recover the existing graph case as `r = 2, c = 2`. State Hales–Jewett separately as a labeled open target.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramsey-r4k | Parent: `RamseyProp` definition and $R(4,k)$ bounds | probabilistic method, pigeonhole |
| ramsey-r4k-oq-01 | Sibling: related Ramsey extension | Ramsey induction |
| ramseys-theorem (if present) | Base finiteness theorem | double induction |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Generalize the definition then double induction**: Define the colored complete $r$-uniform hypergraph and monochromatic clique predicate; prove finiteness by induction on $\sum k_i$ with an inner reduction from $r$-uniform to $(r-1)$-uniform (Ramsey's argument).
   - Why it might work: mirrors the classical proof; multicolor reduces to 2-color by grouping.
   - Risk: index bookkeeping over `Finset (Sym r (Fin N))` or `Finset` of `r`-subsets is fiddly in Lean.

2. **Approach B — Reduce multicolor to two-color first**: Prove $c$-color from 2-color by merging colors, then handle uniformity $r$ by induction — isolates each generalization.
   - Why it might work: two orthogonal, individually simpler inductions.
   - Risk: the merge step needs care to preserve monochromatic cliques.

### Key Difficulties

- Representing $r$-subsets and colorings ergonomically (`Finset`/`Sym`) with decidable predicates.
- Bounds blow up (tower-type); keep the statement to finiteness, not explicit optimal bounds.

### What Would a Proof Need?

- Key lemma 1: pigeonhole reduction $r$-uniform $\to$ $(r-1)$-uniform on a large monochromatic-neighborhood vertex.
- Key lemma 2: multicolor-to-2-color merge preserving monochromatic hypercliques.
- Technical requirements: `Mathlib.Combinatorics.Pigeonhole`, `Finset.exists_...`, existing `RamseyProp` API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The finiteness generalization is a classical, well-understood induction — the main cost is Lean bookkeeping.
- Extends an existing definition, so the API surface is known.
- Hales–Jewett must be excluded from scope (moonshot) and only stated as a target.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable (finiteness in general form): 1–2 weeks
- If hard (Hales–Jewett): unknown

## References

### Papers
- Ramsey, "On a problem of formal logic", 1930 — original hypergraph theorem.
- Graham, Rothschild, Spencer, "Ramsey Theory" — standard reference; Hales–Jewett.

### Online Resources
- Wikipedia "Ramsey's theorem" (hypergraph section) — statement and induction.

### Mathlib
- `Mathlib.Combinatorics.Pigeonhole` — core counting.
- `Mathlib.Combinatorics.SimpleGraph.Ramsey` — existing graph Ramsey API.

## Metadata

```yaml
tags:
  - combinatorics
  - ramsey-theory
  - hypergraph-theory
related_proofs:
  - ramsey-r4k
  - ramsey-r4k-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 5/10
