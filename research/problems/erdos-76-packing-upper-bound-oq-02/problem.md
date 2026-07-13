# Problem: The Balanced-Bipartition Extremal Construction Attains n²/12 Monochromatic Triangles (Erdős #76)

**Slug**: erdos-76-packing-upper-bound-oq-02
**Created**: 2026-07-09T15:22:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For an even integer $n = 2m$, let $c_\star$ be the *balanced-bipartition coloring* of the
complete graph $K_n$: partition the vertex set $V = A \sqcup B$ with $|A| = |B| = m$, color
every edge inside $A$ or inside $B$ **blue**, and every edge between $A$ and $B$ **red**. The
claim is that $c_\star$ admits an edge-disjoint monochromatic triangle packing of size
asymptotic to $n^2/12$, and that this is the maximum over all its packings:

$$
\mathrm{maxPackingSize}(c_\star) \;=\; \Big(\tfrac{1}{12} + o(1)\Big)\, n^2 .
$$

More precisely, the blue class is two disjoint cliques $K_m \sqcup K_m$, each of which packs
$\big(\tfrac{1}{6}+o(1)\big)\binom{m}{2} \approx m^2/6 = n^2/24$ edge-disjoint triangles via a
near-perfect Steiner triple system on its $m$ vertices, while the red class $K_{m,m}$ is
bipartite hence triangle-free and contributes nothing. Summing the two blue cliques:

$$
\mathrm{maxPackingSize}(c_\star) \;\ge\; 2\cdot\big(\tfrac{1}{6}+o(1)\big)\binom{m}{2}
\;=\; \big(\tfrac{1}{12}+o(1)\big)\,n^2 .
$$

### Plain Language

We want to show that a specific, simple 2-coloring of the complete graph — split the
vertices into two equal halves, paint edges *within* a half blue and edges *between* halves
red — actually contains about $n^2/12$ edge-disjoint monochromatic triangles, and cannot do
better than that. The red edges form a complete bipartite graph, which has no triangle at
all, so every triangle we pack must be blue and must live entirely inside one of the two
halves. Each half is a complete graph $K_{n/2}$, and packing a clique with edge-disjoint
triangles is exactly a *Steiner triple system* question: when $n/2 \equiv 1, 3 \pmod 6$ we can
tile essentially all of the edges into triangles, using $\approx \binom{n/2}{2}/3$ of them.
Two halves give twice that, which works out to $n^2/12$.

### Why This Matters

Erdős–Faudree–Ordman (resolved by Gruslys–Letzter, 2020) asserts that *every* 2-coloring of
$K_n$ contains $(1+o(1))n^2/12$ edge-disjoint monochromatic triangles. This is a min-max
statement, and its two directions have completely different flavors. The parent gallery entry
**erdos-76-packing-upper-bound** supplies the crude *upper* bound $\mathrm{maxPackingSize}(c)
\le \binom{n}{2}/3 \approx n^2/6$ for every coloring $c$ by pure edge-counting — but that is a
factor of $2$ above the truth. The value $n^2/12$ can only be certified as the true optimum by
exhibiting a coloring that *reaches* it; the balanced bipartition is that certificate. Pinning
the extremal construction from below at $n^2/12$ therefore (i) shows the Gruslys–Letzter lower
bound is best possible — no coloring is forced to have more than $(1+o(1))n^2/12$ triangles,
and (ii) exposes precisely why the trivial $n^2/6$ budget is halved: the extremal coloring
deliberately wastes one entire color class on a triangle-free bipartite subgraph.

## Known Results

### What's Already Proven

- **Upper bound $\mathrm{maxPackingSize}(c) \le \binom{n}{2}/3 \approx n^2/6$** for every
  2-coloring — parent gallery entry `erdos-76-packing-upper-bound` (`maxPackingSize_le`),
  by double-counting the six ordered edges of each triangle.
- **Existence of Steiner triple systems** $\mathrm{STS}(k)$ for all $k \equiv 1, 3 \pmod 6$ —
  Kirkman (1847); a resolvable-design classic. An $\mathrm{STS}(k)$ partitions the
  $\binom{k}{2}$ edges of $K_k$ into $\binom{k}{2}/3$ edge-disjoint triangles.
- **Maximum partial triangle packing of $K_k$** has size $\big(\tfrac16+o(1)\big)k^2$ for
  *every* $k$ — the leftover of the "$-k \bmod 6$" edges is bounded, so even off the Steiner
  residues the deficit is $O(k)$ (this is the near-perfect matching / near-resolution fact).
- **Complete bipartite graphs are triangle-free**: $K_{m,m}$ contains no odd cycle, so no
  red triangle exists under $c_\star$ — an elementary consequence of 2-colorability.
- **Gruslys–Letzter (2020)** proved the matching lower bound $\ge (1+o(1))n^2/12$ *and* a
  stability result showing near-extremal colorings have a near-bipartite color class,
  identifying $c_\star$ as essentially the unique extremal coloring.

### What's Still Open

- A formal (Lean) construction of the balanced bipartition $c_\star$ and a formal proof that
  its maximum monochromatic packing is $(1+o(1))n^2/12$.
- Combining the parent's clean $n^2/6$ upper bound with this construction to obtain a
  self-contained two-sided asymptotic *for the specific coloring* $c_\star$ (independent of
  the deep Gruslys–Letzter universal lower bound).

### Our Goal

Formalize the **lower bound for the extremal coloring**: construct $c_\star$ on
$V = \mathrm{Fin}\,n$ (n even), and prove $\mathrm{maxPackingSize}(c_\star) \ge
\big(\tfrac{1}{12}+o(1)\big)n^2$ by exhibiting an explicit edge-disjoint blue triangle
packing of that size — first for the clean Steiner case $n/2 \equiv 1,3 \pmod 6$ (exact
$2\binom{n/2}{2}/3$), then extending to general even $n$ with an $O(n)$ deficit. Optionally,
also prove the matching *per-coloring* upper bound $\mathrm{maxPackingSize}(c_\star) \le
2\binom{n/2}{2}/3$ by noting every packed triangle must be blue and confined to one half,
so the packing splits into two clique packings each bounded by the parent's argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-76-packing-upper-bound | Parent; supplies the universal $n^2/6$ upper bound this construction shows is loose by a factor 2, and the exact Triangle/isPacking/maxPackingSize vocabulary to reuse | Double counting, `Finset.offDiag`, `Finset.card_biUnion`, `csSup_le` |
| erdos-76 | Grandparent full formalization; states the deep lower bound as the `gruslys_letzter` axiom and the extremal construction narrative this entry realizes | Ramsey/extremal framing, axiomatized deep bound |
| erdos-7 | Sibling Erdős combinatorics entry sharing the extremal edge-counting / double-counting toolkit | Extremal graph theory, edge counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Steiner-case-first, explicit packing.** Restrict to $n/2 \equiv 1,3
   \pmod 6$, where $K_{n/2}$ has an exact Steiner triple system. Build $c_\star$ on
   $\mathrm{Fin}\,n$ split as $A = \{i : i < m\}$, $B = \{i : i \ge m\}$. Construct the blue
   packing as the disjoint union of an $\mathrm{STS}(m)$ on $A$ and one on $B$, using an
   explicit small construction (e.g. the Bose/Skolem construction, or a $\mathbb{Z}_m$-based
   difference-triple system). Count: $2 \cdot \binom{m}{2}/3 = n^2/12 - n/6$.
   - Why it might work: the count is exact and the packing is fully explicit, so no
     asymptotic bookkeeping is needed in the clean case; edge-disjointness reduces to a
     combinatorial-design property that can be checked from the difference set.
   - Risk: Mathlib has limited Steiner-system infrastructure, so the STS may have to be built
     by hand; verifying edge-disjointness of an explicit difference construction over
     $\mathbb{Z}_m$ can be fiddly.

2. **Approach B — greedy near-perfect packing for arbitrary even $n$.** Avoid exact designs:
   pack each blue clique $K_m$ greedily with edge-disjoint triangles until fewer than a linear
   number of edges remain, invoking the near-perfect triangle-packing bound
   $\ge \big(\tfrac16+o(1)\big)\binom{m}{2}$. Sum the two halves.
   - Why it might work: yields the full asymptotic $n^2/12$ for *all* even $n$ without
     divisibility side conditions; matches the way the construction is stated informally.
   - Risk: the greedy near-perfect bound itself needs proof (a Rödl-nibble / removal-type
     argument, or an explicit resolvable-design near-cover) and is heavier than the exact
     Steiner statement; asymptotic $o(1)$ management in Lean is delicate.

### Key Difficulties

- Encoding "edge-disjoint packing confined to a clique" and proving the two half-packings are
  globally edge-disjoint (they share no vertex, so no edge — but this must be discharged
  formally against the parent's `isPacking` predicate).
- Producing a concrete Steiner triple system (or near-STS) in Lean; Mathlib does not ship
  $\mathrm{STS}$ existence, so a hand construction and its edge-disjointness proof are the
  crux.
- Reconciling the exact vs. asymptotic statements over $\mathbb{N}$: the $\binom{m}{2}/3$
  floor and the $O(n)$ deficit must be tracked with truncated-subtraction care (the same
  `mul_pred_self`-style pitfall the parent flagged).

### What Would a Proof Need?

- Key lemma 1: **Triangle-freeness of the red class** — every triangle of $K_n$ has two
  vertices in a common half under $c_\star$; equivalently, $K_{m,m}$ has no triangle, so any
  monochromatic packed triangle is blue and single-half.
- Key lemma 2: **Steiner packing of $K_m$** — for $m \equiv 1,3 \pmod 6$, an explicit family
  of $\binom{m}{2}/3$ pairwise-edge-disjoint triangles covering all edges of $K_m$ (or, for
  general $m$, a family of size $\big(\tfrac16+o(1)\big)\binom{m}{2}$).
- Key lemma 3: **Disjoint-union packing** — if $P_A$ packs the clique on $A$ and $P_B$ packs
  the clique on $B$ with $A \cap B = \varnothing$, then $P_A \cup P_B$ is an edge-disjoint
  packing of size $|P_A| + |P_B|$ satisfying the parent's `isPacking`.
- Technical requirements: interface with the parent's `Triangle`, `isPacking`,
  `EdgeColoring`, `isMonochromatic`, `monochromaticPacking`, `maxPackingSize`; arithmetic over
  $\mathbb{N}$ (`Nat.choose_two_right`, `Nat.div_le_div`, `omega`) and, for the asymptotic
  form, a `Filter.Tendsto` / `IsBigO`-style $o(1)$ statement.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The upper-bound half (parent entry) is elementary, but the *construction* half genuinely
  requires exhibiting a Steiner-type triangle packing, which has no ready-made Mathlib support
  and must be built and verified by hand.
- The clean Steiner residue case ($m \equiv 1,3 \pmod 6$) is a bounded, explicit combinatorial
  object, so a difference-triple construction over $\mathbb{Z}_m$ is plausible with substantial
  effort; the general-even-$n$ asymptotic (Approach B) is markedly harder and pushes into
  nibble/near-resolution territory.
- Related solved problems: the parent `erdos-76-packing-upper-bound` shows the packing
  vocabulary is already formalized and axiom-free, which lowers the interface cost.
- Mathlib provides finite-graph and `Finset` combinatorics (`SimpleGraph`, `Finset.offDiag`,
  `Finset.card_biUnion`) but no design theory, so the design content is net-new.

**Estimated Effort**:
- Exploration: 3–5 days (survey difference-triple constructions, decide Steiner-case vs.
  asymptotic scope, wire up the parent interface).
- If tractable: 2–4 weeks for the exact Steiner-residue lower bound.
- If hard: unknown for the full general-even-$n$ asymptotic with $o(1)$ management.

## References

### Papers
- Vytautas Gruslys, Shoham Letzter, "Monochromatic triangle packings in red–blue graphs",
  arXiv:2008.05311, 2020 — resolves Erdős–Faudree–Ordman and gives the stability result
  identifying the balanced bipartition as essentially the unique extremal coloring.
- Paul Erdős, Ralph J. Faudree, Ronald J. Gould, Michael S. Jacobson, Jenő Lehel,
  "Edge disjoint monochromatic triangles in 2-colored graphs", Discrete Mathematics 231
  (2001), 135–141 — first quantitative progress and the extremal-construction lower bound.
- Thomas P. Kirkman, "On a problem in combinations", Cambridge and Dublin Mathematical
  Journal 2 (1847), 191–204 — existence of Steiner triple systems for $k \equiv 1,3 \pmod 6$.
- Thomas F. Bloom, "Erdős Problem #76", erdosproblems.com/76, 2024 — catalogue entry,
  solved status, and the balanced-bipartition extremal construction.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` / `.Clique` — complete graphs, cliques, and
  triangle-freeness of bipartite graphs.
- `Mathlib.Combinatorics.SimpleGraph.Bipartite` — bipartite structure of $K_{m,m}$ (no odd
  cycle, hence triangle-free red class).
- `Mathlib.Data.Finset.Card` / `Mathlib.Combinatorics.Choose` — `Finset.offDiag_card`,
  `Finset.card_biUnion`, `Nat.choose_two_right` for the edge/triangle counts.
- `Mathlib.Data.ZMod.Basic` — $\mathbb{Z}_m$ arithmetic for a difference-triple Steiner
  construction.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - extremal-graph-theory
  - triangle-packing
  - edge-colorings
  - design-theory
  - erdos
related_proofs:
  - erdos-76-packing-upper-bound
  - erdos-76
  - erdos-7
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:58-07:00
```
