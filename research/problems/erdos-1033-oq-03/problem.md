# Problem: Improving the Lower Bound on Triangle Degree Sums Beyond (21/16)n

**Slug**: erdos-1033-oq-03
**Created**: 2026-07-09T15:22:57-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $h(n)$ be the largest $k$ such that every simple graph $G$ on $n$ vertices with
$e(G) > n^2/4$ contains a triangle $\{u,v,w\}$ whose vertex degrees satisfy
$d(u) + d(v) + d(w) \geq k$. Fan (1988) proved $h(n) \geq \tfrac{21}{16}n$, while
Erdős–Laskar (1985) proved $h(n) \leq 2(\sqrt{3}-1)n$. The goal is to improve the
lower bound: establish a constant $c > 21/16$ with

$$
h(n) \;\geq\; c\,n - o(n), \qquad \text{i.e.} \quad
\liminf_{n\to\infty} \frac{h(n)}{n} \;\geq\; c \;>\; \frac{21}{16} = 1.3125.
$$

The conjectured optimal value is $c = 2(\sqrt{3}-1) \approx 1.4641$, which would match
the Erdős–Laskar upper bound.

### Plain Language

Turán's theorem says any graph on $n$ vertices with more than $n^2/4$ edges must contain
a triangle. This problem asks a sharper question: not merely "does a triangle exist?" but
"must there be a triangle whose three corners are themselves well-connected?" We measure a
triangle's connectivity by the sum of the degrees of its three vertices. The function
$h(n)$ records the best guarantee: every dense graph has a triangle with degree sum at
least $h(n)$. Fan showed you can always find one with degree sum at least $1.3125\,n$; the
extremal (near-bipartite) constructions of Erdős and Laskar show you cannot always do
better than about $1.4641\,n$. This task is to push the guaranteed floor above Fan's
$1.3125\,n$ — a concrete step toward closing the $\approx 0.15n$ gap.

### Why This Matters

- **Refines the cornerstone of extremal graph theory.** Turán's theorem is the founding
  result of the field; $h(n)$ upgrades a pure *existence* statement into a *quantitative
  structural* one about how deeply the forced triangle is embedded.
- **Prototype for degree-sum extremal problems.** Fan's method of degree counting in
  triangles is a template reused across extremal graph theory (Hamiltonicity, book sizes,
  chromatic criticality). Any improvement sharpens a widely reused toolkit.
- **Directly attacks a stubborn open gap.** The interval $[21/16,\,2(\sqrt3-1)]$ has
  resisted improvement since 1988. Even a modest increase of the lower constant is a
  publishable advance and a formal-mathematics milestone.

## Known Results

### What's Already Proven

- Turán's theorem: $e(G) > \lfloor n^2/4 \rfloor \Rightarrow G$ contains a triangle —
  Turán, *On an extremal problem in graph theory* (1941). Formalized in the parent proof
  (`erdos-1033`, lemma `turan_plus_one`).
- Erdős–Laskar upper bound: $h(n) \leq 2(\sqrt{3}-1)n$ — Erdős–Laskar (1985); captured in
  `erdos-1033` as the axiom `erdos_laskar_upper` with constant `erdosLaskarConstant`.
- Erdős–Laskar lower bound: $h(n) \geq n + O(1)$ — Erdős–Laskar (1985); axiom
  `erdos_laskar_lower` in `erdos-1033`.
- Fan's lower bound: $h(n) \geq \tfrac{21}{16}n$ — Fan, *Degree sum for a triangle in a
  graph* (1988); axiom `fan_lower` in `erdos-1033`, the current record.

### What's Still Open

- Can the lower bound be pushed strictly above $\tfrac{21}{16}n$?
- Is the true asymptotic $h(n) = (2(\sqrt3-1) - o(1))\,n$ (the Erdős–Laskar construction
  being essentially optimal)?
- What is the exact structure of the extremal graphs attaining $h(n)$?

### Our Goal

Formalize a *conditional / quantitative refinement* of the lower bound. Concretely, in a
Lean file extending `erdos-1033`, we aim to:

1. Introduce a parameter `improvedLowerConstant c` and state the theorem
   `h(n) ≥ c·n - o(n)` for a specified `c ∈ (21/16, 2(√3−1)]`.
2. Formalize the *averaging skeleton* that already yields a clean bound: in any graph with
   $e > n^2/4$, the average degree exceeds $n/2$, so a triangle whose vertices sit in the
   high-degree part inherits a degree sum above the trivial $3\cdot(n/2)$ threshold. This
   makes precise which counting inequality Fan strengthens.
3. Package the improvement target as `theorem improved_fan_lower : h n ≥ ⌈c*n⌉ := by sorry`
   suitable for downstream proof search, with `c` set to a value strictly above `21/16`
   that a proof can defend (e.g. isolating one concrete step of Fan's argument that admits
   a better constant).

The realistic formal deliverable is the *statement + averaging infrastructure + the exact
counting lemmas Fan uses*, so that improving the constant reduces to sharpening one
identified inequality — not a full new resolution of the gap.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1033 | Parent problem: defines $h(n)$, the Turán threshold, triangle degree sums, and states Fan's $(21/16)n$ bound as the current record | Extremal graph theory, Turán threshold, triangle degree-sum formalization |
| erdos-905 | Every dense graph has an edge in $\geq n/6$ triangles; this codegree/book-lemma bound underlies degree-counting lower bounds for triangle degree sums | Codegree counting, book lemma, dense-graph triangle structure |
| erdos-1034 | Companion problem on triangle neighbor counts above the Turán threshold; parallel structural analysis of forced triangles | Neighborhood counting, extremal thresholds |
| ramseys-theorem | The $r=3$ Ramsey/Turán instance forcing triangles; degree sums refine the structure forced past the threshold | Ramsey-type counting, clique existence in dense graphs |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Sharpen Fan's degree-counting inequality.** Fan derives
   $(21/16)n$ by bounding, for a suitably chosen edge $uv$ of high codegree, the degree sum
   $d(u)+d(v)+d(w)$ over triangles $uvw$. Reproduce his weighted count and identify the
   inequality where a constant is conceded, then feed in the stronger codegree bound
   available from `erdos-905` ($\geq n/6$ triangles per dense edge) to gain a strictly
   larger constant.
   - Why it might work: the improvement is *local* — a single inequality — so it can be
     formalized as one lemma over reals/finsets without re-deriving the whole theory.
   - Risk: Fan's constant may already be tight for his specific weighting scheme; a genuine
     improvement might require a new global argument, not just a tighter inequality.

2. **Approach B — Averaging + high-degree subgraph extraction.** Delete low-degree vertices
   to pass to a subgraph with large minimum degree while staying above the Turán threshold;
   apply a triangle-existence result there so the triangle's vertices all have degree
   $\geq \delta$ for a controlled $\delta > n/2$, giving degree sum $> 3\delta$.
   - Why it might work: minimum-degree/deletion arguments are standard and Mathlib-friendly
     (finset cardinality, degree-sum handshake lemma).
   - Risk: naive deletion tends to reproduce the trivial $\sim 3n/2$-type bound and may not
     beat $21/16 = 1.3125$ without Fan's finer triangle-by-triangle weighting.

### Key Difficulties

- Formalizing Fan's weighted triangle-degree-sum count over finsets, including the case
  analysis on codegrees, is intricate and error-prone.
- Asymptotic $o(n)$ terms must be handled rigorously in Lean (real-valued limits vs.
  finite $n$), and the parent axioms are known to be too strong for small $n$.
- Isolating a *single* improvable inequality without accidentally re-proving a false sharper
  bound requires care: any claimed constant must be genuinely defensible.

### What Would a Proof Need?

- Key lemma 1: a Mathlib-level degree-sum handshake identity, $\sum_v d(v) = 2e(G)$, to get
  average degree $> n/2$ from $e > n^2/4$ (available via `SimpleGraph.sum_degrees_eq_twice_card_edges`).
- Key lemma 2: an edge of high codegree exists above the Turán threshold (codegree $\geq n/6$
  book bound, cf. `erdos-905`), pinning down a triangle-rich edge.
- Key lemma 3: Fan's weighted count bounding $\min$ over triangles of $d(u)+d(v)+d(w)$ from
  below, restated as a real inequality with the improved constant as a free parameter.
- Technical requirements: real-arithmetic manipulation (`Real.sqrt`, `nlinarith`), finset
  degree bookkeeping, and a clean `improvedLowerConstant` definition placed between `21/16`
  and `2(√3−1)`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The underlying mathematics is a genuine open gap unsolved since 1988; a *full* improvement
  of the constant is research-grade and may be infeasible.
- However, the *formalization deliverable* (statement + averaging infrastructure + explicit
  restatement of Fan's counting lemmas as parameterized inequalities) is tractable and
  valuable on its own, mirroring how `erdos-1033` already formalizes the bounds as axioms.
- Mathlib provides the core graph-theory scaffolding: `SimpleGraph.degree`,
  `SimpleGraph.IsClique`/triangles, `SimpleGraph.sum_degrees_eq_twice_card_edges`, and real
  analysis for the constants — so the surrounding structure is well-supported even though the
  sharp inequality itself is hard.

**Estimated Effort**:
- Exploration: 3–5 days to reconstruct Fan's argument and locate the improvable inequality.
- If tractable: 2–4 weeks to formalize the averaging skeleton and parameterized lower-bound
  statement with a modestly improved, defensible constant.
- If hard: unknown — a full closure of the $[21/16,\,2(\sqrt3-1)]$ gap is an open research
  problem.

## References

### Papers
- G. Fan, *Degree sum for a triangle in a graph*, Journal of Graph Theory **12** (1988),
  249–263 — proves $h(n) \geq (21/16)n$; the inequality to be sharpened.
- P. Erdős and R. Laskar, *A note on the size of a chordal subgraph*, Congressus
  Numerantium (1985) — introduces $h(n)$ and the upper bound $2(\sqrt{3}-1)n$.
- P. Turán, *On an extremal problem in graph theory*, Matematikai és Fizikai Lapok **48**
  (1941), 436–452 — the threshold $e > n^2/4$ forcing a triangle.
- B. Bollobás, *Extremal Graph Theory*, Academic Press (1978) — standard reference for
  Turán-type and degree-sum methods.

### Online Resources
- https://erdosproblems.com/1033 — Erdős Problem #1033 entry, statement and status.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` — degree, `sum_degrees_eq_twice_card_edges`
  handshake lemma for the averaging step.
- `Mathlib.Combinatorics.SimpleGraph.Clique` — triangles as 3-cliques for degree-sum terms.
- `Mathlib.Combinatorics.SimpleGraph.Basic` — adjacency and neighbor-finset machinery.
- `Mathlib.Data.Real.Sqrt` — the constant $2(\sqrt{3}-1)$ and real inequalities.

## Metadata

```yaml
tags:
  - graph-theory
  - extremal-graph-theory
  - combinatorics
  - triangles
  - turan-theory
related_proofs:
  - erdos-1033
  - erdos-905
  - erdos-1034
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:57-07:00
```
