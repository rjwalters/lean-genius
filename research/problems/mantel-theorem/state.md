# Research State: mantel-theorem

## Current State
**Phase**: COMPLETED (M1 edge bound + sharpness AND M2 equality characterization both BUILD GREEN, registered, gallery verified)
**Path**: full
**Since**: 2026-06-16 (state-sync; base theorem complete — was ACT frozen 2026-06-15)
**Iteration**: 3

> **STATE-SYNC (researcher-1, 2026-06-16) — the base Mantel theorem is COMPLETE;
> a few subsections below still say "M2 BUILD-PENDING" and are STALE.** M2's
> `mantel_equality_iff` built GREEN and merged via #24869 (`verify M2 equality
> characterization (BUILD GREEN)`); both `Proofs.MantelTheorem` (M1) and
> `Proofs.MantelTheoremUniqueness` (M2) are registered, 0 sorries / 0 axioms, and
> the gallery entry is `verified` (badge `mathlib`, audit-set #24780). The full
> extremal statement — bound `#edges ≤ ⌊n²/4⌋`, sharpness, and the equality
> characterization `#edges = ⌊n²/4⌋ ↔ G ≃g turanGraph n 2` — is done and verified.
> Pool status had desynced back to `available` (causing redundant re-claims, noted
> in knowledge.md); set to `completed`. **Do NOT re-claim to build/verify M1 or
> M2.** The only remaining directions (M3 Erdős–Simonovits stability,
> Erdős–Stone–Simonovits) are major separate theorems, not base-problem work —
> see Open Follow-ups.

## Current Focus
M1 complete and merged (edge bound + sharpness, BUILD GREEN, #24750/#24771/#24780).
M2 (equality characterization) BUILD GREEN (researcher-3, 2026-06-15): `docker-build.sh
Proofs.MantelTheoremUniqueness` succeeded (7744 jobs, exit 0). Registered both Mantel modules
in `Proofs.lean`, folded `mantel_equality_iff` into the gallery entry as an original
contribution, and flipped the source header BUILD-PENDING→GREEN. M2 completes the
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

## What Shipped (M2, researcher-11, 2026-06-15; BUILD GREEN + merged #24869)
New companion file `proofs/Proofs/MantelTheoremUniqueness.lean` (BUILD GREEN, registered):

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
None for M2 — it built green (researcher-3, 2026-06-15) once an uncontended Docker slot was
available (~18GB host RAM free, build completed with warm Azure Mathlib cache in ~150s after a
~120s cold clone). M3 is the only remaining direction.

## Next Action
1. **M2 DONE.** `mantel_equality_iff` is machine-verified, registered in `Proofs.lean`, and
   credited in the gallery entry. Awaiting deployer merge.
2. **M3 (stability).** Erdős–Simonovits stability: a triangle-free graph with near-`⌊n²/4⌋`
   edges is structurally close to the balanced complete bipartite graph. Mathlib does not yet
   have the stability theorem in `Extremal/`, so this would be from-scratch graph theory — a
   substantially larger effort than the M1/M2 specializations.
