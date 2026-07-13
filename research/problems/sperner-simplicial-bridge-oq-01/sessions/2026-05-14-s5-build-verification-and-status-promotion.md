# S5 — Build verification + gallery status promotion

**Date**: 2026-05-14
**Researcher**: researcher-9
**Phase**: ACT (build verification — not a Lean code-change)
**Predecessors**: PR #18234 (S1 OBSERVE), #18363 (S2 SCAFFOLD), #18434 (S2b OBSERVE), #18451 (S2c PREP), #18537 (S3 ACT, build pending), #18564 (S3b PREP), #18677 (S4 GALLERY, status=formalized/badge=wip), #18746 (audit clean), #18741/#18819/#18833 (enrichment), #18940 (STATE-SYNC).

## What this session ships

The S3 ACT (PR #18537) merged `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` on 2026-05-13 with a `build pending` qualifier. The S4 GALLERY (PR #18677) followed two hours later, shipping the gallery entry conservatively as `status: "formalized"` / `badge: "wip"` because no Doctor/Mechanic had confirmed the docker build. No subsequent session has executed the build verification — until now.

**This session ran `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` against `origin/main` HEAD from a clean container** (no prior cache for this specific Lean file). Result: see below. On the basis of that verification, this PR:

1. Promotes the gallery entry from `status: "formalized"` / `badge: "wip"` → `status: "verified"` / `badge: "verified"`.
2. Updates the `assumptions` field text to drop the "build pending" caveat.
3. Updates state.md to record the S4 GALLERY (#18677), STATE-SYNC (#18940), and this build verification (PR #19009-ish) in the iteration history.
4. Updates `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` `currentState.{phase, focus, nextAction}`, `iteration`, `lastUpdate`, and `knowledge.progressSummary` to match.
5. Writes this session log.

## Build verification details

Command: `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01`
Mathlib pin: v4.26.0
Container: fresh `lean-build-*` (no prior cache for this file; the Mathlib olean cache was downloaded fresh from Azure during this run).
Build target: `Proofs.SpernerSimplicialBridgeOQ01` + transitive deps (Proofs.SpernerSimplicialBridge + ~3050 Mathlib targets).

**Outcome**: ✅ **`Build completed successfully (7745 jobs).`** No errors, no warnings beyond the standard `unusedSectionVars` linter note. The container ran for ~5 minutes total (mostly the fresh Mathlib olean cache download from Azure; the actual Lean elaboration for `Proofs.SpernerSimplicialBridgeOQ01` was a small fraction of that time).

## What is **not** in this session

- **No Lean source changes.** `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` is unchanged at 184 LOC / 6 theorems / 3 defs / 0 sorries / 0 axioms.
- **No gallery section restructuring.** The 6 enrichment annotations and 5-section split (PRs #18741, #18819, #18833) are preserved as-is.
- **No new open-question rows.** The "forward levers" listed in state.md (mixed-dimension aggregator `sperner_mixed_panchromatic`, decidable promotion of `boundaryDoorCount`) remain optional / TODO and are not pursued here.

## Files modified

1. `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json`:
   - `status: "formalized"` → `"verified"`
   - `badge: "wip"` → `"verified"`
   - `assumptions`: rewritten to drop "build pending" qualifier
2. `research/problems/sperner-simplicial-bridge-oq-01/state.md`:
   - Phase line: "ACT (S2 SCAFFOLD + S3 ACT shipped; build pending)" → "ACT (build verified; gallery promoted to status=verified)"
   - Since: 2026-05-13T22:50:00Z → 2026-05-14T04:00:00Z
   - Iteration: 3 → 9
   - Current Focus: replaced
   - Iteration History: added rows for S4 GALLERY (#18677), STATE-SYNC (#18940), and this session
   - Path to Verification: marked S4b row ✅
   - Next Action: rewritten to point at the optional S5+ follow-ups (mixed-dim aggregator, decidable boundaryDoorCount)
3. `src/data/research/problems/sperner-simplicial-bridge-oq-01.json`:
   - `currentState.{phase, focus, nextAction}` synced with state.md
   - `currentState.iteration: 3 → 9`
   - `knowledge.progressSummary` prepended with this session's outcome
   - `lastUpdate: 2026-05-13T22:50:00Z → 2026-05-14T04:00:00Z`
   - `leanFiles[0]` counts unchanged (184/6/3/0/0 from S3 ACT)
4. `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-14-s5-build-verification-and-status-promotion.md` (this file, new).

## Race-safety note (as of this commit)

- `gh pr list -R rjwalters/lean-genius --search "sperner-simplicial-bridge-oq-01 in:title" --state open`: 0 OPEN PRs as of session start.
- Last research-merge on slug: PR #18940 (STATE-SYNC by researcher-1, 2026-05-13T23:05:29Z), ~5 hours before this session.
- Last enrichment-merge: PR #18833 (enricher, 2026-05-13T12:44:18Z), gallery sections only — zero conflict surface with this build-promotion PR.
- This PR touches no Lean source and no enrichment files; conflict surface is limited to `meta.json` (status/badge/assumptions), `state.md` (iteration tracker), and the research JSON (currentState block).

## Why this matters

Per `CLAUDE.md` "Axiom Integrity Policy":
> When in doubt, use 'axiomatized' — overclaiming 'verified' damages credibility.

The S4 GALLERY's `formalized`/`wip` posture was the correct conservative choice at the time. Promoting now requires direct evidence that `lake build` succeeds, which this session provides. The promotion is therefore the natural next step — converting the gallery entry's conservatism into the credibility that the underlying Lean file's 0-sorry / 0-axiom claim earns.

## Next action

The slug is now fully `verified`. The remaining items are all OPTIONAL extensions:

1. **Mixed-dimension aggregator** (~30-40 LOC, separate slug or OQ-05): `sperner_mixed_panchromatic K (hK : MixedPseudomanifold K) : ∃ d, ∃ s ∈ topCellsOfDim K d, Odd (boundaryDoorCount d K) ∧ Panchromatic s`. Shifts the existential from "fix `d`, find `s`" to "find `(d, s)` together". Likely qualifies as a sibling open question rather than an extension of this slug.
2. **Decidable promotion of `boundaryDoorCount`** (~10-15 LOC): remove the `noncomputable` qualifier by exposing the underlying `Fintype.card` form. Unblocks concrete evaluation on small example complexes for gallery demos.
3. **n = 7 / n = 11 analogs**: a parallel open question for mixed pseudomanifolds in higher-dimension stratifications. Beyond OQ-01's scope.

None are required; the slug's primary deliverable (per-stratum Sperner for mixed-dimension complexes, 0 sorries, 0 axioms, build-verified) is complete.
