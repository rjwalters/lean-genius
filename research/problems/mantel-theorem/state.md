# Research State: mantel-theorem

## Current State
**Phase**: ACT (M2 written, build-pending)
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
M1 complete and merged (edge bound + sharpness, BUILD GREEN, #24750/#24771/#24780).
M2 (equality characterization) written in companion file `MantelTheoremUniqueness.lean`,
BUILD-PENDING (Docker cold-build timeout + Aristotle down). Once verified, M2 completes the
full extremal statement of Mantel's theorem.

## Active Approach
Specialize Mathlib's general Turán edge bound `SimpleGraph.CliqueFree.card_edgeFinset_le`
to `r = 2` and collapse the arithmetic to `⌊n²/4⌋`.

## What Shipped (M1, researcher-6, 2026-06-15)
New file `proofs/Proofs/MantelTheorem.lean` (84 lines, 5 theorems, 0 axioms, 0 sorries),
BUILD GREEN (7743 jobs, exit 0, docker-build.sh @8GB):

1. `turan_two_simp` — arithmetic identity collapsing the general Turán r=2 RHS to `n²/4`.
2. `mantel_card_edgeFinset_le` — **Mantel's theorem**: `G.CliqueFree 3 ⟹ #G.edgeFinset ≤
   (Fintype.card V)² / 4`.
3. `turanGraph_two_cliqueFree` — `turanGraph n 2` is triangle-free.
4. `card_edgeFinset_turanGraph_two` — `turanGraph n 2` has exactly `n²/4` edges.
5. `mantel_bound_is_tight` — sharpness: a triangle-free graph attaining `⌊n²/4⌋` exists.

Gallery data added at `src/data/proofs/mantel-theorem/meta.json` (status `verified`,
badge `original`).

## What Shipped (M2, researcher-11, 2026-06-15)
New companion file `proofs/Proofs/MantelTheoremUniqueness.lean` (BUILD-PENDING):

- `mantel_equality_iff` — **equality characterization**: for triangle-free `G` on `n` vertices,
  `#G.edgeFinset = ⌊n²/4⌋ ↔ Nonempty (G ≃g turanGraph n 2)`. Completes the extremal statement.

Proof (~12 lines): rewrite the RHS to `G.IsTuranMaximal 2` via Mathlib's Turán uniqueness
`isTuranMaximal_iff_nonempty_iso_turanGraph`; forward direction builds `IsExtremal` from
`mantel_card_edgeFinset_le` (every triangle-free graph has `≤ ⌊n²/4⌋` edges, and `G` attains
it); reverse direction transfers `turanGraph n 2`'s edge count via `Iso.card_edgeFinset_eq`
and `card_edgeFinset_turanGraph_two`.

All Mathlib lemma names/signatures verified against pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0). Companion file (imports verified
`Proofs.MantelTheorem`) so a latent error cannot regress the verified M1 entry.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib Turán + IsTuranMaximal uniqueness — written, pending build)

## Blockers
Docker cold-build timeout (every build re-clones Mathlib + downloads cache, ~750s setup,
exceeding the 20m wrapper timeout before the target compiles); Aristotle backend 404.
M2 is build-pending until a warm-cache build slot is available.

## Next Action
1. **Verify M2.** `docker-build.sh Proofs.MantelTheoremUniqueness` when a warm Mathlib cache /
   uncontended slot is available; if green, fold `mantel_equality_iff` into the gallery entry
   (theoremCount 5→6) and resolve the equality-characterization open question.
2. **M3 (stability).** Erdős–Simonovits stability: a triangle-free graph with near-`⌊n²/4⌋`
   edges is structurally close to the balanced complete bipartite graph.
