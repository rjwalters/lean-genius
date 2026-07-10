# Problem: Constructive Simonovits — A Polynomial-Time Algorithm for Forced Saturated Planar Subgraphs

**Slug**: erdos-1019-oq-01
**Created**: 2026-07-09T17:03:06-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, \mathcal{A} \text{ running in } \operatorname{poly}(n) \text{ time such that, given } G = (V,E) \text{ with } |V| = n \text{ and } |E| \ge \left\lfloor \tfrac{n^2}{4} \right\rfloor + \left\lfloor \tfrac{n+1}{2} \right\rfloor, \; \mathcal{A}(G) \text{ outputs a subgraph } H \subseteq G \text{ with } H \cong K_4 \text{ or } H \cong C_\ell + 2K_1 \ (\ell \ge 3).
$$

Equivalently: can Simonovits's existence proof be turned into an efficient **search** procedure?

### Plain Language

Simonovits proved that any $n$-vertex graph with at least $\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ edges must contain a saturated planar subgraph on more than three vertices — concretely, either a $K_4$ or a cycle $C_\ell$ with two extra vertices each joined to the whole cycle ($C_\ell + 2K_1$). His argument shows such a subgraph *exists*, but does not obviously tell you how to *find* one quickly. The question is whether the proof (or some other method) yields a deterministic polynomial-time algorithm that, on input such a dense graph, actually produces one of these two structures.

### Why This Matters

Turning existence proofs in extremal graph theory into algorithms is a recurring theme (algorithmic regularity, the algorithmic Lovász Local Lemma, constructive Ramsey bounds). A constructive version of Simonovits's theorem would (1) give a certificate-producing routine for the parent result in the gallery, (2) sharpen our understanding of *where* in a dense graph the forced topological structure lives, and (3) connect the extremal threshold to the algorithmic complexity of subgraph search. Because both target subgraphs are saturated planar ($|E| = 3|V| - 6$), an efficient finder also produces explicit maximal-planar witnesses inside dense graphs.

## Known Results

### What's Already Proven

- **Simonovits's dichotomy** (existence) — Every $n$-vertex graph with $\ge \lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ edges contains $K_4$ or $C_\ell + 2K_1$. Formalized (with stated axioms) as the parent gallery proof `erdos-1019` (`Proofs/Erdos1019Problem.lean`, axiom `simonovits_theorem`).
- **Threshold tightness** — Erdős's construction with $\lfloor n^2/4 \rfloor + \lfloor (n-1)/2 \rfloor$ edges (Turán graph $K_{\lfloor n/2\rfloor,\lceil n/2\rceil}$ plus a matching in one part) avoids all such subgraphs. The one-edge gap is exact.
- **$K_4$ detection is polynomial** — Any fixed subgraph on $k$ vertices can be found in $O(n^k)$ time by brute force; for $K_4$ this is $O(n^4)$, so the *$K_4$ branch* alone is already constructive. The difficulty is the $C_\ell + 2K_1$ branch, where $\ell$ is unbounded.

### What's Still Open

- Is there a $\operatorname{poly}(n)$ algorithm that finds a $C_\ell + 2K_1$ (for *some* $\ell \ge 3$) whenever the graph is $K_4$-free but above threshold?
- Can Simonovits's structural argument (neighborhood analysis of edges beyond the bipartite part) be made algorithmic, i.e. each existence step replaced by an efficient constructive step?
- What is the best achievable running time / dependence on $n$, and can it be made near-linear?

### Our Goal

Formalize the *decision-to-search* reduction and settle the tractable half: give and verify a polynomial-time procedure for the $K_4$ branch, and formalize a candidate algorithm for the $C_\ell + 2K_1$ branch (e.g. searching for two common neighbors of a long cycle, or "two vertices dominating a common cycle"), stating precisely the structural lemma an efficiency proof would require.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1019 | Parent: the existence theorem this problem makes constructive | Turán threshold, saturated planar graphs, Wagner forbidden-minor planarity |
| erdos-1019 (extensions) | Erdős tightness construction and threshold-gap arithmetic | Complete bipartite graphs, `omega` edge counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Branch split + brute force on the bounded branch**: First run $O(n^4)$ search for $K_4$. If found, done. Otherwise the graph is $K_4$-free but above threshold, so by Simonovits it must contain $C_\ell + 2K_1$; search for that.
   - Why it might work: reduces the whole problem to the single hard case ($K_4$-free, above threshold), which is exactly the regime where Simonovits's structural argument is most explicit.
   - Risk: $\ell$ is unbounded, so naive enumeration of cycles is exponential; need a structural handle.

2. **Approach B — "Two common dominators of a cycle"**: A $C_\ell + 2K_1$ is a cycle $C_\ell$ plus two vertices $u, w$ each adjacent to all of $C_\ell$. Search for a pair $\{u,w\}$ whose common neighborhood $N(u)\cap N(w)$ contains a cycle; extract that cycle. Common-neighborhood computation is $O(n^2)$ per pair, and cycle-finding in a subgraph is linear.
   - Why it might work: turns the search into "find two vertices whose common neighborhood is non-forest," which is polynomial to test over all $O(n^2)$ pairs.
   - Risk: needs a proof that above threshold and $K_4$-free, *some* pair's common neighborhood necessarily contains a cycle — this is the crux structural lemma, essentially the constructive content of Simonovits's argument.

### Key Difficulties

- The cycle length $\ell$ is not bounded by a constant, so the target subgraph is not a *fixed* pattern; standard fixed-subgraph isomorphism arguments do not directly apply.
- Simonovits's proof is a structural/extremal argument (analyzing neighborhoods of "extra" edges); extracting an explicit witness may require re-deriving constants and case splits algorithmically.
- Distinguishing constructively which branch ($K_4$ vs $C_\ell + 2K_1$) a given graph falls into, near the threshold, may hinge on delicate counting.

### What Would a Proof Need?

- **Key lemma 1** (branch reduction): A $K_4$-free graph above the threshold contains a pair of vertices whose common neighborhood induces a subgraph with a cycle (giving $C_\ell + 2K_1$).
- **Key lemma 2** (efficiency): Each step of the Simonovits neighborhood argument can be performed in $\operatorname{poly}(n)$ time (adjacency lookups, common-neighborhood sets, cycle detection via DFS/BFS).
- **Technical requirements**: a formal model of "polynomial-time algorithm on finite simple graphs," a correctness relation between the algorithm output and `containsK4` / `containsCyclePlus2K1` from the parent file, and cycle-extraction (Mathlib `SimpleGraph.Walk` / `IsCycle`).

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The $K_4$ branch and the *decision-to-search* framing are genuinely tractable and formalizable (brute-force $O(n^4)$, common-neighborhood scans).
- The $C_\ell + 2K_1$ branch requires making Simonovits's structural argument fully constructive — this is a real research question, not a mechanical translation, because $\ell$ is unbounded and the original proof is existential.
- Mathlib supports finite simple graphs, walks, cycles, and neighbor finsets, so partial formalization (the tractable half + a precisely stated crux lemma) is realistic; a full efficiency proof is not.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable (partial formalization + $K_4$ branch): 1–2 weeks
- If hard (full constructive $C_\ell + 2K_1$ finder with proof): unknown / research-level

## References

### Papers
- M. Simonovits, *A method for solving extremal problems in graph theory, stability problems*, in Theory of Graphs (Proc. Colloq. Tihany, 1966), 279–319 — origin of the stability method underlying the parent theorem.
- P. Erdős, M. Simonovits, *A limit theorem in graph theory*, Studia Sci. Math. Hungar. 1 (1966), 51–57 — Erdős–Simonovits stability, context for the near-extremal structure.
- N. Alon, R. Duke, H. Lefmann, V. Rödl, R. Yuster, *The algorithmic aspects of the regularity lemma*, J. Algorithms 16 (1994), 80–109 — model example of converting an extremal existence proof into a polynomial-time algorithm.

### Online Resources
- https://erdosproblems.com/1019 — statement, status (solved), and references for the parent Erdős problem.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` — finite simple graphs, adjacency, `neighborFinset`, `edgeFinset`.
- `Mathlib.Combinatorics.SimpleGraph.Walk` — walks, paths, and `IsCycle`, needed to extract the $C_\ell$ in $C_\ell + 2K_1$.
- `Mathlib.Combinatorics.SimpleGraph.Subgraph` — subgraph containment and induced subgraphs, for stating the algorithm's output.
- `Mathlib.Combinatorics.SimpleGraph.Turan` — Turán's theorem and the bipartite threshold behind the edge bound.

## Metadata

```yaml
tags:
  - graph-theory
  - planar-graphs
  - erdos
  - extremal-combinatorics
  - turan-theory
related_proofs:
  - erdos-1019
difficulty: high
source: gallery-gap
created: 2026-07-09T17:03:06-07:00
```
