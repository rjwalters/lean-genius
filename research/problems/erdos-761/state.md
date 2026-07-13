# Current State

**Phase**: ACT (ℕ∞-side lifts realized; structural lemma surface widened)
**Path**: full
**Since**: 2026-04-27 (BLOCKED), 2026-05-08 (UNBLOCKED — Iter 7),
           2026-06-05 (Iter 8), 2026-06-06 (Iter 9 — this PR)
**Last Updated**: 2026-06-06 (Iteration 9, researcher-1)
**Iteration**: 9

## Current Focus

**Iter 9 (this PR)**: Realized the two next-action lemmas predicted by
Iter 8's state.md, lifting the ℕ-valued χ-bounds to Mathlib's
`SimpleGraph.chromaticNumber : ℕ∞`.

1. `dichrom_le_chromaticNumber (G : SimpleGraph V) :
    (G.dichromNumber : ℕ∞) ≤ G.chromaticNumber` — proved via
    `le_iInf₂` on Mathlib's `⨅ n ∈ setOf G.Colorable, (n : ℕ∞)`
    definition, then `exact_mod_cast` of `dichrom_le_of_colorable`.
    The bound is vacuous when `G.chromaticNumber = ⊤` and agrees
    with δ(G) ≤ χ(G) on every finitely-chromatic graph.
2. `cochrom_le_chromaticNumber (G : SimpleGraph V) :
    (G.cochromNumber : ℕ∞) ≤ G.chromaticNumber` — mirror lift via
    `cochrom_le_of_colorable`.

Both are 3-line `le_iInf₂` + cast proofs. No new axioms, no sorries,
no changes to definitions or the open-conjecture axioms.

**2 axioms remain** in `proofs/Proofs/Erdos761Problem.lean` (314 lines,
10 theorems, 6 defs, 1 private lemma, 0 sorries on this PR):

1. `erdos_761_question1` (Erdős–Neumann-Lara) — must a graph with
   large chromatic number have large dichromatic number? OPEN.
2. `erdos_761_question2` (Erdős–Gimbel) — must a graph with large
   cochromatic number contain a subgraph with large dichromatic
   number? OPEN.

Both are genuinely open questions and remain as axioms.

## Iteration History

- **Iter 1–4** (2026-03–04, multiple PRs): bootstrap + axiom reductions
  + IsAcyclicColoring correction (PR #7309 etc.).
- **Iter 5** (2026-04-26, PR #12755 etc.): re-audit clean.
- **Iter 6** (2026-04-27, PR #13195): drift discovery — the local
  `Orientation` structure collides with
  `Mathlib.LinearAlgebra.Orientation` after Mathlib's transitive
  import surface expanded. Documented blocker.
- **Iter 7** (2026-05-08, researcher-11): drift partially unblocked
  via `namespace Erdos761` wrapper, BUT the file was never built
  (state.md said "Build pending"); the wrapper itself introduced a
  fresh dot-notation breakage on every `G.dichromNumber` /
  `G.cochromNumber` call.
- **Iter 8** (2026-06-05, researcher-1): (a) added
  `dichrom_le_of_colorable` + `cochrom_le_of_colorable`; (b)
  simplified `bipartite_dichrom_le_two` to a corollary; (c)
  repaired the Iter-7 wrapper via `_root_.` defs; (d) repaired
  Mathlib 4.26 `Equiv.injective` drift. lineCount 262 → 291.
  theoremCount 7 → 8. First successful Docker build since 2026-04-27.
- **Iter 9** (2026-06-06, researcher-1, this PR): lifted the two
  `_of_colorable` bounds to Mathlib's `SimpleGraph.chromaticNumber :
  ℕ∞` via `le_iInf₂`. lineCount 291 → 314. theoremCount 8 → 10.
  Both proofs are 3 lines; bound is vacuous when chromaticNumber = ⊤.

## Active Approach (next sessions)

The two ℕ∞ lifts are now in. Remaining work to widen the structural
surface around δ(G) and ζ(G):

- **Iter 10 candidate** — `cochrom_le_dichrom_via_clique` or an analogue
  comparing δ(G) and ζ(G) directly. Currently we have both bounded by
  χ(G) and both bounded by |V|, plus `dichrom_mono` for δ under
  subgraph inclusion. No lemma relates δ and ζ. The classical
  inequality ζ(G) ≤ δ(G) follows from observing that an acyclic
  k-coloring's classes induce DAG subgraphs, whose underlying
  undirected graphs are either cliques or have a missing edge — but
  this is not immediate from the definitions and may need a stronger
  acyclic-coloring lemma first. Out of scope for a single iteration.
- **Iter 10 alternate** — `cochrom_mono` analogue to `dichrom_mono`:
  ζ(H) ≤ ζ(G) for H ⊆ G. The cochromatic property restricts cleanly
  to subgraphs (an induced clique stays a clique; an induced
  independent set stays independent), so this should be ~15 lines.
- **Iter 10 alternate** — `dichrom_le_one_of_edgeless`: δ(G) ≤ 1 when
  G has no edges (any 1-coloring is vacuously acyclic). 5-line lemma.

All three are independent of the two open axioms.

## Blockers

None.

## Next Action

**Iter 10**: `cochrom_mono` (ζ monotone under subgraph inclusion) —
mirrors `dichrom_mono` but does not need the orientation-extension
machinery; cochromatic colorings restrict directly. Estimated ~15
lines.

## Attempt Counts

- Total attempts: 9
- Current approach attempts: 1 (Iter 9 ℕ∞ lifts, this PR)
- Approaches tried: drift discovery (Iter 6); namespace wrapper
  unblock (Iter 7); structural ℕ-valued χ-bounds (Iter 8); ℕ∞ lifts
  to Mathlib chromaticNumber (Iter 9).

## References

- `proofs/Proofs/Erdos761Problem.lean` — main file (314 lines, 10
  theorems, 6 defs, 1 private lemma, 2 axioms, 0 sorries).
- `src/data/proofs/erdos-761/meta.json` — gallery integration.
- Neumann-Lara 1982: "The dichromatic number of a digraph",
  *J. Combin. Theory Ser. B* 33.
- Erdős–Gimbel: cochromatic conjecture (open).
