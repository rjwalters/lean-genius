# Problem: Computational Complexity of Locating the Kostochka–Pyber Non-Planar Subgraph

**Slug**: erdos-1018-oq-05
**Created**: 2026-07-09T17:03:06-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Given } G \text{ on } n \text{ vertices with } |E(G)| \ge n^{1+\varepsilon} \text{ and } \varepsilon > 0, \text{ Kostochka–Pyber (1988) guarantees a non-planar } H \subseteq G \text{ with } |V(H)| \le C_\varepsilon = O_\varepsilon(1). \text{ What is the time complexity of an algorithm that } \textbf{outputs} \text{ such an } H?
$$

Equivalently: is there an algorithm running in time $f(\varepsilon) \cdot \mathrm{poly}(n)$ (i.e. fixed-parameter tractable in $\varepsilon$, or at least polynomial in $n$ for each fixed $\varepsilon$) that, on any $n$-vertex graph with at least $n^{1+\varepsilon}$ edges, returns a vertex set $S$ with $|S| \le C_\varepsilon$ such that the induced subgraph $G[S]$ (or a specified subgraph on $S$) is non-planar?

### Plain Language

Kostochka and Pyber proved that any graph dense enough — with $n^{1+\varepsilon}$ edges — must contain a non-planar piece using only a bounded number $C_\varepsilon$ of vertices, no matter how large the whole graph is. Their proof shows such a piece *exists*, but it uses averaging and probabilistic/extremal counting that does not obviously hand you the small piece efficiently. This problem asks: how hard is it to actually *find* one of these small non-planar subgraphs? Can we do it in polynomial time in $n$ (for each fixed $\varepsilon$), or is locating the obstruction genuinely harder than knowing it exists?

### Why This Matters

Separating existence from construction is a central theme in extremal and probabilistic combinatorics: many classical results (Ramsey-type bounds, the Lovász Local Lemma, expander/subdivision theorems) originally gave non-constructive guarantees that were later matched by efficient algorithms. Making the Kostochka–Pyber guarantee constructive would (i) turn a pure existence theorem into a certified subroutine usable inside larger graph algorithms, (ii) connect topological obstruction theory (Kuratowski / $K_5$, $K_{3,3}$ subdivisions) to the well-developed algorithmic theory of topological minors and $H$-subdivision testing, and (iii) sharpen our understanding of the density-vs-obstruction-size tradeoff $C_\varepsilon \to \infty$ as $\varepsilon \to 0$ from an algorithmic angle. Efficient planarity testing (Hopcroft–Tarjan, linear time) and Kuratowski-subgraph extraction already exist; the open question is whether the *bounded-size* guarantee can be achieved efficiently rather than by brute-forcing over all $O(n^{C_\varepsilon})$ candidate vertex subsets.

## Known Results

### What's Already Proven

- **Kostochka–Pyber (1988)** — every $n$-vertex graph with $n^{1+\varepsilon}$ edges contains a $K_5$-subdivision (hence a non-planar subgraph) on $O_\varepsilon(1)$ vertices. This is the existence result formalized in the parent proof `erdos-1018`.
- **Kuratowski (1930) / Wagner (1937)** — a graph is non-planar iff it contains a subdivision (resp. minor) of $K_5$ or $K_{3,3}$; this reduces "non-planar subgraph" to "$K_5$ or $K_{3,3}$ subdivision".
- **Hopcroft–Tarjan (1974)** — planarity of an $n$-vertex graph is decidable in $O(n)$ time, and a Kuratowski subgraph (an *arbitrary*, not necessarily small, $K_5$/$K_{3,3}$ subdivision) can be extracted in linear time (Williamson 1984; Boyer–Myrvold 2004).
- **Robertson–Seymour / Grohe–Kawarabayashi–Marx–Wollan (2011)** — for a *fixed* pattern $H$, testing whether $G$ contains an $H$-subdivision is in FPT (parameterized by $|H|$), running in $f(|H|)\cdot n^{3}$ time; relevant because $C_\varepsilon$ is a constant for fixed $\varepsilon$.
- **Mader (1967/1972)** — the extremal (Turán-type) threshold for forcing a $K_t$-subdivision is $O(t\sqrt{\log t}\cdot n)$ edges, underpinning the density regime in which small obstructions must appear.

### What's Still Open

- Whether there is an algorithm outputting a non-planar subgraph on $\le C_\varepsilon$ vertices in time $f(\varepsilon)\cdot\mathrm{poly}(n)$ (FPT in $\varepsilon$), rather than the naive $n^{O(C_\varepsilon)}$ exhaustive search over vertex subsets.
- Whether the *smallest* non-planar subgraph (optimizing $|V(H)|$, not just meeting the $C_\varepsilon$ bound) can be found efficiently, or whether that optimization is NP-hard.
- The precise dependence of any construction algorithm's running time on $\varepsilon$ (equivalently on the guaranteed size $C_\varepsilon \sim 1/\varepsilon^2$), and whether it matches the density-size tradeoff.

### Our Goal

Determine the computational complexity of the *search* (construction) version of Kostochka–Pyber: classify how efficiently a bounded-size non-planar subgraph can be located, ideally producing either (a) a polynomial-time (per fixed $\varepsilon$) constructive algorithm derived from the extremal proof, or (b) a hardness reduction showing the *minimum*-size version is intractable. As a first formalizable milestone, define the decision/search problem precisely in Lean and relate it to existing subdivision-testing complexity results.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1018 | Parent problem: existence of a small non-planar (K₅-subdivision) subgraph in dense graphs; this problem asks for the algorithmic/constructive version | Kuratowski characterization, Kostochka–Pyber axiom, Euler edge bound $3n-6$, super-linear density |
| erdos-52 | Related Erdős extremal graph theory problem on forced substructure under density hypotheses | Extremal counting, density thresholds |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Constructivize the extremal proof (algorithmize existence)**: Follow the Kostochka–Pyber / Mader argument step by step (pass to a high-min-degree subgraph, greedily build a $K_5$ subdivision through short connecting paths) and show each step is polynomial-time.
   - Why it might work: Mader-type subdivision existence proofs are largely greedy/iterative; high-degree vertices and short paths are found by BFS. Planarity of the resulting bounded subgraph is checkable in linear time (Hopcroft–Tarjan).
   - Risk: The probabilistic sampling step that reduces to a bounded-size graph may only give existence "on average", requiring derandomization; the branch/path selection may need backtracking that inflates the running time to $n^{\Omega(C_\varepsilon)}$.

2. **Approach B — Reduce to fixed-pattern subdivision testing (FPT framing)**: For fixed $\varepsilon$, $C_\varepsilon$ is a constant, so enumerate candidate patterns and invoke the Grohe–Kawarabayashi–Marx–Wollan $f(|H|)n^3$ topological-minor algorithm on $\le C_\varepsilon$-vertex targets.
   - Why it might work: Immediately yields polynomial time in $n$ for each fixed $\varepsilon$, settling the "poly per fixed $\varepsilon$" version affirmatively.
   - Risk: The dependence $f(\varepsilon)$ may be astronomical (tower-type in $1/\varepsilon$), and it does not find the *smallest* obstruction; the genuinely open FPT-in-$\varepsilon$-with-good-dependence question remains.

### Key Difficulties

- Distinguishing "polynomial in $n$ for each fixed $\varepsilon$" (likely true via FPT subdivision testing) from "FPT in $\varepsilon$ with a reasonable function" (open) from "minimum-size version" (possibly NP-hard).
- Mathlib 4.26 lacks topological planarity, graph subdivisions, and any complexity-theoretic framework, so even *stating* a running-time claim formally requires building substantial scaffolding (mirroring the axioms in `erdos-1018`).
- Non-constructive counting steps in the original proof resist direct algorithmization without derandomization.

### What Would a Proof Need?

- Key lemma 1: an algorithmic Mader lemma — a polynomial-time procedure that, given min-degree $\ge d$, outputs a $K_t$-subdivision on $O(t^2)$ vertices.
- Key lemma 2: a bounded-search-to-FPT bridge — for constant target size $k$, $H$-subdivision search is polynomial in $n$ (specializing GKMW).
- Technical requirements: a formal cost model (RAM/word cost or an abstract "poly(n)" predicate), a subgraph-extraction primitive, and a certified planarity checker to verify the output is genuinely non-planar.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The "poly in $n$ for each fixed $\varepsilon$" version is essentially known (FPT subdivision testing), but the interesting versions — a *good* dependence on $\varepsilon$, or the minimum-size obstruction — are genuinely open and touch active algorithmic-graph-minors research.
- Formalizing *any* complexity statement in Lean is currently very heavy: there is no complexity theory, no topological planarity, and no subdivision machinery in Mathlib 4.26, so the realistic near-term goal is a precise *statement* plus reduction lemmas, not a machine-checked complexity separation.
- Similar problems (algorithmic Lovász Local Lemma, constructive Ramsey bounds) took decades to make constructive, suggesting the sharp version is hard.

**Estimated Effort**:
- Exploration: 1–2 weeks to formalize the problem statement and the FPT reduction sketch.
- If tractable (the "poly per fixed $\varepsilon$" packaging): weeks.
- If hard (sharp FPT dependence or minimum-size hardness): unknown / open research.

## References

### Papers
- A. V. Kostochka, L. Pyber, "Small topological complete subgraphs of dense graphs", Combinatorica 8 (1988), 83–86 — the source existence theorem whose constructive version is sought here.
- W. Mader, "Homomorphieeigenschaften und mittlere Kantendichte von Graphen", Math. Ann. 174 (1967), 265–268 — extremal density forcing $K_t$-subdivisions.
- J. Hopcroft, R. Tarjan, "Efficient planarity testing", J. ACM 21 (1974), 549–568 — linear-time planarity and Kuratowski-subgraph extraction.
- M. Grohe, K. Kawarabayashi, D. Marx, P. Wollan, "Finding topological subgraphs is fixed-parameter tractable", STOC 2011, 479–488 — $f(|H|)n^3$ topological-minor testing.

### Online Resources
- https://erdosproblems.com/1018 — Erdős problem #1018, the source of the parent existence result.
- https://en.wikipedia.org/wiki/Kuratowski%27s_theorem — Kuratowski/Wagner characterization used to certify non-planarity.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` — simple graphs, adjacency, subgraphs (the ambient vocabulary, as used in `erdos-1018`).
- `Mathlib.Combinatorics.SimpleGraph.Finite` — finite vertex types and edge/degree counting for stating the density hypothesis $|E| \ge n^{1+\varepsilon}$.
- `Mathlib.Combinatorics.SimpleGraph.Subgraph` — induced subgraphs $G[S]$, needed to state "outputs a bounded-size non-planar subgraph".

## Metadata

```yaml
tags:
  - graph-theory
  - planar-graphs
  - erdos
  - topological-graph-theory
  - extremal-combinatorics
related_proofs:
  - erdos-1018
  - erdos-52
difficulty: high
source: gallery-gap
created: 2026-07-09T17:03:06-07:00
```
