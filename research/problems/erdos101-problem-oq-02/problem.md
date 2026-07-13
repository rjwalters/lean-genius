# Problem: Formalize the Szemerédi–Trotter Incidence Bound

**Slug**: erdos101-problem-oq-02
**Created**: 2026-07-04T19:56:31-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
I(P, L) \;\le\; C\left(|P|^{2/3}\,|L|^{2/3} + |P| + |L|\right)
$$

for any finite set of points $P \subset \mathbb{R}^2$ and any finite set of lines
$L$, where $I(P,L) = \#\{(p,\ell) \in P \times L : p \in \ell\}$ is the number of
incidences and $C$ is an absolute constant.

### Plain Language

Given $m$ points and $n$ straight lines in the plane, count how many
point-on-line pairs there can be. The naive bound is $O(mn)$ (or $O(mn^{1/2})$
from the fact that two points determine at most one common line). Szemerédi and
Trotter proved the sharp bound $O(m^{2/3}n^{2/3} + m + n)$, tight up to the
constant. We want a machine-checked proof of this incidence bound in Lean 4.

### Why This Matters

The Szemerédi–Trotter theorem is the cornerstone of incidence geometry and
underlies the parent gallery entry (Erdős Problem #101 on four-point lines): a
subquadratic incidence bound immediately controls the number of "rich" lines
through a planar point set. It also drives the sum–product phenomenon, the
Elekes bound, and many additive-combinatorics results. A formal proof gives a
reusable Mathlib-ready building block for combinatorial geometry.

## Known Results

### What's Already Proven

- Szemerédi–Trotter theorem (1983) — the incidence bound is classical; the
  cell-decomposition and crossing-number proofs are standard.
- Crossing Number Inequality — $\mathrm{cr}(G) \ge c\,|E|^3/|V|^2$ for graphs with
  $|E| \ge 4|V|$; Székely's proof of Szemerédi–Trotter reduces to this.
- Parent entry `erdos101-problem` — establishes the four-point-line counting
  framework this bound feeds into.

### What's Still Open

- No formalization of Szemerédi–Trotter exists in Mathlib.
- The crossing-number inequality is itself not yet in Mathlib, so a self-contained
  route may need it (or an alternative cell-decomposition argument).

### Our Goal

Formalize the incidence upper bound $I(P,L) \le C(|P|^{2/3}|L|^{2/3} + |P| + |L|)$.
The recommended route is Székely's proof via the crossing number inequality,
since it avoids the analytic subtleties of the original cell decomposition. A
first milestone is the balanced case $|P| = |L| = n$, giving $I = O(n^{4/3})$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos101-problem | Parent: four-point lines rely on rich-line counts | Extremal counting |
| erdos-distinct-distances | Same incidence-geometry toolkit | Crossing numbers, cell decomposition |

## Initial Thoughts

### Potential Approaches

1. **Székely crossing-number proof**: Build the graph whose edges are the segments
   of each line between consecutive incident points; apply the crossing number
   inequality to the planar-drawn multigraph.
   - Why it might work: reduces the whole theorem to one clean inequality.
   - Risk: the crossing number inequality is not in Mathlib and must be built,
     itself needing Euler's formula for planar graphs.

2. **Cell decomposition**: Partition the plane with a random subset of lines and
   bound incidences cell-by-cell.
   - Why it might work: elementary, no crossing numbers.
   - Risk: probabilistic/counting bookkeeping is heavy to formalize.

### Key Difficulties

- Mathlib lacks a planar-graph / crossing-number library.
- Turning "points on a line, ordered along the line" into a combinatorial graph
  requires a clean order structure on collinear points.

### What Would a Proof Need?

- Key lemma 1: Crossing number inequality (or Euler's formula for planar graphs).
- Key lemma 2: The at-most-one-line-through-two-points fact to bound low-incidence
  contributions.
- Technical requirements: Finset cardinality manipulation and a real-power AM–GM
  step to balance the two error terms.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is classical and well understood.
- Missing Mathlib infrastructure (crossing numbers, planar graphs) is the main
  cost, not the argument itself.
- A scoped-down balanced case ($m = n$) is a realistic first deliverable.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks (with the crossing-number lemma as a sub-project)
- If hard: unknown (full Mathlib planar-graph support)

## References

### Papers
- Szemerédi & Trotter, "Extremal problems in discrete geometry", *Combinatorica* 3 (1983) — original bound.
- Székely, "Crossing numbers and hard Erdős problems in discrete geometry", *Combin. Probab. Comput.* 6 (1997) — the short crossing-number proof.

### Online Resources
- Terence Tao, "The Szemerédi–Trotter theorem and the cell decomposition" (blog) — exposition of both proofs.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.*` — graph scaffolding (no crossing numbers yet).
- `Mathlib.Analysis.MeanInequalities` — AM–GM to balance the error terms.

## Metadata

```yaml
tags:
  - combinatorics
  - incidence-geometry
  - szemeredi-trotter
  - crossing-numbers
related_proofs:
  - erdos101-problem
difficulty: high
source: proof-suggestion
created: 2026-07-04T19:56:31-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
