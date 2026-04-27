# Erdős #533 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $\delta>0$. If $n$ is sufficiently large and $G$ is a graph on $n$ vertices with no $K_5$ and at least $\delta n^2$ edges then $G$ contains a set of $\gg_\delta n$ vertices containing no triangle.




A problem of Erd\H{o}s, Hajnal, Simonovits, S\'{o}s, and Szemer\'{e}di, who could prove this is true for $\delta>1/16$, and could further prove it for $\delta>0$ if we replace $K_5$ with $K_4$.

They further observed that it fails for $\delta =1/4$ if we replace $K_5$ with $K_7$: by a construction of Erd\H{o}s and Rogers \cite{ErRo62} (see [620]) there exists some constant $c>0$ such that, for all large $n$, there is a graph on $n$ vertices which contains no $K_4$ and every set of at least $n^{1-c}$ vertices contains a triangle. If we take two vertex disjoint copies of this graph and add all edges between the two copies then this yields a graph on $2n$ vertices with $\geq n^2$ edges, which contains no $K_7$, yet every set of at least $2n^{1-c}$ vertices contains a triangle.


See also [579] and the entry in the graphs problem collection.




References


[ErRo62] Erd\H{o}s, P. and Rogers, C. A., The construction of certain graphs. Canadian J. Math. (1962), 702-707.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #16
- Problem #4
- Problem #620
- Problem #579
- Problem #532
- Problem #534
- Problem #2
- Problem #39
- Problem #1

## References

- Er91
- EHSSS94
- ErRo62

## Sessions

### Session 1 (2026-04-27) — Axiom Survey + Turán Reduction Path

**Mode**: REVISIT (claimed RICH, score 29)
**Outcome**: SURVEY — corrected stale claim that "no axioms provable from Mathlib"; identified `turan_k5_free` as eliminable from Mathlib's existing Turán API

#### Current File State (`Erdos533Problem.lean`, 372 lines)
- **0 sorries**, **4 axioms** (1 is the open conjecture itself, 3 are supporting):
  1. `turan_k5_free` (line 278) — K₅-free graph has ≤ (3/8)n² edges
  2. `ehsss_result` (line 292) — Erdős–Hajnal–Simonovits–Sós–Szemerédi 1976 (δ > 1/16 case)
  3. `k4_free_triangle_free_subset` (line 300) — companion deep result
  4. `erdos_533_conjecture` (line 361) — the open conjecture (cannot be proved)
- File defines bespoke `SGraph` structure with bridge `SGraph.toSimpleGraph` to Mathlib.

#### Correction to Prior Session Knowledge
The prior progressSummary claims "Axioms are all deep published results — none provable from Mathlib." This is **wrong for `turan_k5_free`**: Mathlib has Turán's theorem on `SimpleGraph`. Cross-reference: `Erdos1155OQ02.lean:264-265` already uses `turanGraph_cliqueFree`, confirming Mathlib's Turán API is accessible from this project.

#### Path to Eliminating `turan_k5_free`
The axiom states: K₅-free `SGraph` on n vertices has `edgeCount ≤ (3/8) * n²` (real-valued).

Proof path (estimated 100-200 lines):
1. **Bridge**: Use `SGraph.toSimpleGraph` (already in file). Lift `¬HasClique G 5` to `(G.toSimpleGraph).CliqueFree 5`.
2. **Mathlib Turán bound**: For `K_{r+1}`-free graphs, Mathlib gives the bound on `edgeFinset.card`. The relevant API surfaces are in `Mathlib.Combinatorics.SimpleGraph.Turan` (`turanGraph`, `turanGraph_cliqueFree`, and the `IsTuranMaximal.card_edgeFinset_le` style lemma — exact Mathlib name needs verification by build attempt).
3. **EdgeCount bridge**: The file's `edgeCount` is `Finset.card (filter ... (Finset.univ.product Finset.univ))` over ordered pairs (i<j). Mathlib's `SimpleGraph.edgeFinset.card` counts unordered edges. These should match (already proved indirectly via `edgeCount_le` for the `n*(n-1)/2` upper bound).
4. **Arithmetic**: From `card ≤ (1 - 1/4) · n²/2 = (3/8)n²`, cast to ℝ.

This is genuinely tractable in a focused session (estimated 100-200 lines, mostly bridge work). It would reduce the axiom count from 4 to 3.

#### Why This Session Did NOT Attempt the Proof
- Mathlib symlink loops in `proofs/.lake/packages/mathlib/` prevent reliable lemma name search from this worktree (every grep into Combinatorics/SimpleGraph errors with "Too many levels of symbolic links"). Without confirming the exact Mathlib lemma name, attempting the proof would devolve into guess-and-check with Docker rebuild cycles.
- This session has already done two Docker builds (5+ min each) for the angle-trisection and erdos-456 drift verification; another speculative build cycle is poor ROI.
- Better next-session approach: claim this problem from a fresh worktree where Mathlib is accessible, or invoke the Aristotle pipeline with `turan_k5_free` as a target after confirming it satisfies Aristotle's criteria (clean theorem, no main-conjecture status).

#### Why `ehsss_result`, `k4_free_triangle_free_subset` Cannot Be Eliminated
These are deep theorems from 1976 (Erdős–Hajnal–Simonovits–Sós–Szemerédi, *Discrete Math.*). Their proofs require ~1000+ lines of extremal graph theory infrastructure not currently in Mathlib. They legitimately remain as axioms.

### Files Modified This Session
- `research/problems/erdos-533/knowledge.md` — Session 1 entry (this)
- `src/data/research/problems/erdos-533.json` — `progressSummary` and `mathlibGaps` corrected to reflect `turan_k5_free` is eliminable

### Next Steps (priority order)
1. **Eliminate `turan_k5_free`** via Mathlib's `turanGraph` / `IsTuranMaximal` API (~100-200 lines). This drops the axiom count 4 → 3.
2. **Aristotle target** for the bridge lemma `SGraph.edgeCount = G.toSimpleGraph.edgeFinset.card` — should be a clean Aristotle target.
3. The remaining axioms (ehsss, k4-free, conjecture) are out-of-scope for elimination.

---

*Generated from erdosproblems.com on 2026-01-13*
