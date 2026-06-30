# Problem: The Friendship Theorem for Infinite Graphs

**Slug**: friendship-theorem-oq-04
**Created**: 2026-06-14
**Status**: Active
**Source**: gallery-gap <!-- open question extending friendship-theorem -->

## Problem Statement

### Formal Statement

Finite case (the gallery theorem): if a finite graph $G$ has the property that every two distinct vertices have **exactly one** common neighbour, then $G$ has a "universal friend" — a vertex adjacent to all others (a windmill/friendship graph).

Infinite extension (this problem):

$$
\text{Does } \forall\, u \neq v,\ |N(u)\cap N(v)| = 1 \ \text{force a universal vertex when } V(G) \text{ is infinite?}
$$

The known answer is **no** without extra hypotheses: there exist infinite graphs satisfying the unique-common-neighbour condition with no universal friend (constructed by Erdős–Rényi–Sós and others). The research question is to formalize a precise statement: characterize which additional structural assumptions (e.g. local finiteness, bounded degree, regularity) restore the windmill conclusion, and formalize at least one counterexample and one positive result.

### Plain Language

The friendship theorem says: in a finite "everyone-shares-exactly-one-mutual-friend" social network, there must be one person who is friends with everybody (a politician). For infinite networks this *fails* — you can build endless friend-of-a-friend structures with no universal politician. The task is to pin down, in Lean, exactly where the finite proof breaks and what extra conditions bring the conclusion back.

### Why This Matters

The finite proof is a beautiful mix of double counting and **spectral** (eigenvalue) methods — and both ingredients fail for infinite graphs. Formalizing the boundary between the finite and infinite regimes clarifies *why* the spectral argument is essential and gives the gallery a worked example of "a theorem that does not generalize, and the precise reason." It also exercises Mathlib's `SimpleGraph` API on infinite vertex types.

## Known Results

### What's Already Proven

- Friendship theorem (finite) — gallery proof `friendship-theorem`; classical Erdős–Rényi–Sós (1966)
- Infinite counterexamples exist: there are infinite friendship graphs with no universal vertex (Erdős–Rényi–Sós; later Chvátal–Kotzig–and others)
- The finite proof's spectral step: the adjacency matrix eigenvalue/regularity argument — relies on finite-dimensional linear algebra

### What's Still Open (in Lean)

- A formal statement separating the finite theorem from the infinite case
- A formalized infinite counterexample (graph + verification of the unique-common-neighbour property + absence of universal vertex)
- A positive result under an explicit extra hypothesis (e.g. local finiteness or bounded degree), if one is cleanly provable

### Our Goal

Formalize: (1) the negative result — exhibit/define an infinite graph satisfying the hypothesis with no universal vertex; and (2) identify and state (ideally prove) a structural hypothesis under which the windmill conclusion is recovered. Document precisely which step of the finite gallery proof fails in the infinite setting.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| friendship-theorem | The finite theorem being extended | Double counting + spectral / eigenvalue |
| graph-theory cluster (e.g. konigsberg, ramsey) | Shared `SimpleGraph` infrastructure | Combinatorial graph arguments |

## Initial Thoughts

### Potential Approaches

1. **Counterexample first** (recommended): define a concrete infinite friendship graph (e.g. a suitable algebraic/geometric incidence structure, or a directed-tree-based construction) and prove in Lean it satisfies $|N(u)\cap N(v)|=1$ for all $u\ne v$ yet has no universal vertex.
   - Why it might work: it is a construction + verification, no spectral theory needed.
   - Risk: choosing a construction whose unique-common-neighbour property is *cleanly* provable in Lean.

2. **Positive result under bounded degree/regularity**: try to show the windmill conclusion holds for infinite *locally finite* friendship graphs (if true), reusing a localized version of the counting argument.
   - Risk: the truth and the cleanest hypothesis need literature confirmation; the spectral step does not localize.

### Key Difficulties

- The eigenvalue argument is intrinsically finite-dimensional; there is no drop-in infinite analogue.
- Verifying the unique-common-neighbour property for an explicitly defined infinite graph can be combinatorially fiddly.

### What Would a Proof Need?

- Key lemma 1: a concrete infinite `SimpleGraph` with decidable adjacency and a proof of the unique-common-neighbour property.
- Key lemma 2: proof that no vertex is universal in that graph.
- (Optional positive) Key lemma 3: under local finiteness, recover a universal vertex or show counterexamples persist.
- Technical requirements: `Mathlib.Combinatorics.SimpleGraph.*`, `Set`/`Finset` neighbourhood lemmas, infinite vertex types.

## Tractability Assessment

**Difficulty**: Medium–Hard

**Justification**:
- The counterexample direction is a self-contained construction-and-verification task (medium).
- A clean *positive* theorem under extra hypotheses is more open-ended and depends on literature (harder).

**Estimated Effort**:
- Exploration: 1–2 days (survey infinite-friendship-graph constructions)
- If tractable (counterexample): ~1 week; positive result: unknown

## References

### Papers
- P. Erdős, A. Rényi, V. T. Sós, "On a problem of graph theory", Studia Sci. Math. Hungar. 1 (1966), 215–235.
- J. Q. Longyear, T. D. Parsons, "The friendship theorem", Indag. Math. (infinite remarks).
- H. S. M. Coxeter / later surveys on infinite friendship graphs.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` — graphs, neighbourhoods, adjacency
- `Mathlib.Combinatorics.SimpleGraph.Finite` — common-neighbour cardinalities (finite case)

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - friendship-theorem
  - infinite-graphs
  - spectral-methods
related_proofs:
  - friendship-theorem
difficulty: hard
source: gallery-gap
created: 2026-06-14
```
