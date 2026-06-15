# Research State: mantel-theorem

## Current State
**Phase**: ACT (M1 shipped)
**Path**: full
**Since**: 2026-06-15
**Iteration**: 1

## Current Focus
M1 complete: Mantel's edge bound + sharpness formalized and BUILD GREEN. Next natural
target is the equality characterization (M2).

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

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib Turán specialization — succeeded)

## Blockers
None.

## Next Action
**M2 — equality characterization.** Prove that equality `#G.edgeFinset = ⌊n²/4⌋` holds iff
`G` is isomorphic to the balanced complete bipartite graph, via
`SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph`. Requires connecting the floor bound
to `IsTuranMaximal` (a Turán-maximal triangle-free graph attains the bound) and unfolding the
`turanGraph n 2` structure as `K_{⌊n/2⌋,⌈n/2⌉}`.
