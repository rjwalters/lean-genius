# Problem: Improving the Upper Bound for Clique Partitions of Chordal Graphs

**Slug**: erdos-81-oq-01
**Created**: 2026-07-09T15:22:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $G$ be a chordal graph on $n$ vertices (no induced cycle of length $> 3$), and
let $\mathrm{cp}(G)$ denote its **clique partition number**: the minimum number of
cliques needed to partition the edge set $E(G)$ (each edge lies in exactly one
clique of the partition). Define the extremal quantity

$$
f(n) \;=\; \max_{\substack{G \text{ chordal} \\ |V(G)| = n}} \mathrm{cp}(G).
$$

The Erdős–Ordman–Zalcstein upper bound gives $f(n) \le \left(\tfrac14 - \varepsilon\right) n^2$
for some fixed $\varepsilon > 0$, while the split-graph construction
$K_{n/3} \cup \overline{K_{2n/3}}$ (with complete bipartite join) forces
$f(n) \ge \tfrac{n^2}{6} + O(n)$. The open question is to close this gap:

$$
\text{Conjecture: } \quad f(n) \;=\; \frac{n^2}{6} + O(n).
$$

Equivalently, prove the improved **upper bound**
$$
f(n) \;\le\; \frac{n^2}{6} + O(n),
$$
which would match the known lower bound and settle Erdős Problem #81.

### Plain Language

A *chordal graph* is one in which every cycle of four or more vertices has a
"shortcut" chord. We want to cover all of a graph's edges using complete
subgraphs (cliques), so that each edge is used exactly once, and we ask how few
cliques are ever needed in the worst case. It is known that some chordal graphs
genuinely require about $n^2/6$ cliques, and that no chordal graph ever needs
more than about $n^2/4$. The conjecture says the true worst case is $n^2/6$: the
upper bound $n^2/4$ can be pushed down to $n^2/6$. Our task is to formalize this
gap precisely and to work toward the improved upper bound.

### Why This Matters

Clique partition (or clique edge-cover) numbers control the efficiency of
representing a graph as a union of complete subgraphs, which appears in sparse
matrix factorization (fill-in and elimination trees), keyword-conflict and
addressing problems, and confluent drawing. Chordal graphs are the canonical
"tree-like" graph class with a perfect elimination ordering, so understanding
their extremal clique-partition behavior isolates exactly *which* structural
feature limits partition efficiency. Closing the $\tfrac14$ vs $\tfrac16$ gap is
the headline open case of Erdős Problem #81 and would pin down the leading
constant for an entire natural graph class.

## Known Results

### What's Already Proven

- **Erdős–Ordman–Zalcstein upper bound** $f(n) \le (\tfrac14 - \varepsilon)n^2$ —
  P. Erdős, E. T. Ordman, Y. Zalcstein, *Clique partitions of chordal graphs*,
  Combin. Probab. Comput. 2 (1993), 409–415. Formalized in the parent gallery
  proof `erdos-81` as the axiom `erdos_ordman_zalcstein`.
- **Lower bound** $f(n) \ge \tfrac{n^2}{6} + O(n)$ via the split graph
  $K_{n/3}$ joined to $2n/3$ isolated vertices — parent proof `erdos-81`
  (`extremal_construction_exists`, `lower_bound`).
- **Split-graph upper bound** $\mathrm{cp}(G) \le \tfrac{3n^2}{16} + O(n)$ for
  split graphs $G$ — G. Chen, P. Erdős, E. Ordman (1994); this lies strictly
  between the conjectured $\tfrac16$ and the known $\tfrac14$.
- **Chordal $\Leftrightarrow$ perfect elimination ordering** — G. A. Dirac (1961)
  and D. R. Fulkerson & O. A. Gross (1965); parent proof `erdos-81`
  (`peo_gives_clique_partition`), yielding a greedy $2$-approximation for
  $\mathrm{cp}$.

### What's Still Open

- Whether the leading coefficient of $f(n)$ is $\tfrac16$ (the factor-$\tfrac32$
  gap between $\tfrac14$ and $\tfrac16$ for general chordal graphs).
- Whether split graphs are the extremal case, and whether $\tfrac{3}{16}$ is
  tight for split graphs.

### Our Goal

We do **not** aim to resolve the open conjecture. The formalization goal is to
state the gap rigorously in Lean and prove the *tractable structural pieces*:
(1) a clean definition of the clique partition number $\mathrm{cp}(G)$ as a
`Nat`-valued minimum over edge-partitioning clique families; (2) the lower-bound
witness — an explicit construction of the split graph $K_{n/3} \cup \overline{K_{2n/3}}$
and a proof that it needs $\gtrsim n^2/6$ cliques; and (3) a monotone/summary
theorem tying the known upper bound $(\tfrac14-\varepsilon)n^2$ and the target
$n^2/6 + O(n)$ into a single statement of the remaining gap, replacing the
current axioms of `erdos-81` where possible with proved lemmas.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-81 | Parent problem: same clique-partition question, contains the axioms and definitions we refine | Chordal graphs, perfect elimination ordering, split-graph extremal construction |
| erdos-1017 | Related clique partition / clique cover problem cross-referenced by the parent | Clique partitions, extremal counting |
| ramseys-theorem | Both concern unavoidable substructures and structural constraints in graphs | Extremal graph theory, pigeonhole, induction on vertices |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Formalize and lower-bound the extremal split graph.**
   Construct $K_{n/3}$ joined completely to $2n/3$ independent vertices as a
   concrete `SimpleGraph (Fin n)`, then prove any clique-partition of it uses at
   least $\approx n^2/6$ cliques by counting the $2n/3 \cdot n/3$ bipartite edges
   and showing each partition clique covers at most one bipartite "star" per
   independent vertex.
   - Why it might work: the counting is elementary (each independent vertex has
     an independent neighborhood in the join, so its incident cliques are stars),
     and it converts an axiom into a proved theorem.
   - Risk: careful bookkeeping of the $O(n)$ error term and clean handling of
     divisibility $n \equiv 0 \pmod 3$; Mathlib lacks a ready clique-partition
     API so we must build it.

2. **Approach B — Prove the split-graph upper bound $\tfrac{3n^2}{16}$
   (Chen–Erdős–Ordman) as a stepping stone.**
   Partition a split graph's clique side greedily and cover the bipartite edges
   with $\tfrac{3}{16}n^2 + O(n)$ cliques via the balanced-partition argument.
   - Why it might work: it is a *closed* result (not the open conjecture), so it
     is fully formalizable and narrows the gap in the gallery from $\tfrac14$ to
     $\tfrac{3}{16}$ for the split case.
   - Risk: the optimal split partition argument is intricate; a full proof may be
     large. Partial progress (a weaker explicit constant $c \cdot n^2$) is still
     valuable.

### Key Difficulties

- Mathlib has `SimpleGraph.IsClique` but no clique-*partition* number; the whole
  `cp` API (existence of a minimum, monotonicity, edge-disjointness) must be
  developed from `Finset` and `SimpleGraph.edgeSet`.
- Managing asymptotic $O(n)$ error terms inside a `Nat`/`Real` mixed setting
  without overclaiming exact constants.
- The general upper-bound improvement is genuinely open, so only the lower bound
  and the split-graph special case are realistically provable.

### What Would a Proof Need?

- Key lemma 1: `cp` is well-defined — every finite graph has *some* edge clique
  partition (singletons/edges), so the minimum exists (`Nat.find` / `Finset.min'`).
- Key lemma 2: in the split join $K_a \cup \overline{K_b}$ with complete
  bipartite connection, any clique meeting an independent vertex $v$ is a subset
  of $\{v\} \cup N(v)$'s clique side; counting gives $\mathrm{cp} \ge$ (bipartite
  edge count) $/$ (max star reuse) $\approx n^2/6$.
- Key lemma 3 (upper side): a PEO-based greedy partition yields
  $\mathrm{cp}(G) \le c\, n^2$ for an explicit $c$ (at most $\tfrac14$), giving the
  bracketing statement of the gap.
- Technical requirements: `SimpleGraph.Clique`, `Finset` cardinality/partition
  lemmas, and a small custom library for edge clique partitions.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full conjecture ($n^2/6$ upper bound) is an open Erdős problem, so a
  complete resolution is out of reach; however the *lower-bound witness* and a
  weaker explicit upper bound are Medium-difficulty formalization tasks.
- Similar extremal graph constructions (Turán-type counting, extremal split
  graphs) have been formalized before, and the parent `erdos-81` already
  encodes the statement, so the scaffolding exists.
- Mathlib provides `SimpleGraph`, `SimpleGraph.IsClique`, and rich `Finset`
  cardinality tooling, but no clique-partition number — a moderate amount of
  supporting API must be built.

**Estimated Effort**:
- Exploration: 2–4 days (design the `cp` API, formalize the split construction)
- If tractable: 2–4 weeks (lower bound + split-graph upper bound $3n^2/16$)
- If hard: unknown (the general $n^2/6$ upper bound is open)

## References

### Papers
- P. Erdős, E. T. Ordman, Y. Zalcstein, "Clique partitions of chordal graphs",
  Combinatorics, Probability and Computing 2 (1993), 409–415 — origin of the
  problem and the $(\tfrac14-\varepsilon)n^2$ upper bound.
- G. Chen, P. Erdős, E. Ordman, "Clique partitions of split graphs" (1994) —
  the $3n^2/16 + O(n)$ bound for split graphs.
- G. A. Dirac, "On rigid circuit graphs", Abh. Math. Sem. Univ. Hamburg 25
  (1961), 71–76 — perfect elimination orderings characterize chordal graphs.
- D. R. Fulkerson, O. A. Gross, "Incidence matrices and interval graphs",
  Pacific J. Math. 15 (1965), 835–855 — chordal/interval graph structure.

### Online Resources
- https://erdosproblems.com/81 — Erdős Problem #81 statement and status (open).

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Basic — `SimpleGraph`, adjacency, `edgeSet`.
- Mathlib.Combinatorics.SimpleGraph.Clique — `SimpleGraph.IsClique`, clique sets.
- Mathlib.Data.Finset.Basic — finite sets, cardinality, partitions.
- Mathlib.Data.Nat.Basic — `Nat.find` for defining the minimum clique count.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - chordal-graphs
  - clique-partitions
  - split-graphs
related_proofs:
  - erdos-81
  - erdos-1017
  - ramseys-theorem
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:58-07:00
```
