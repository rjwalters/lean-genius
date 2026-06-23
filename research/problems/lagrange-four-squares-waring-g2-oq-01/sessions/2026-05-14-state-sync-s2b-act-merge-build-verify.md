# STATE-SYNC — S2b ACT merge + S2b ACT BUILD-VERIFY visibility

**Date**: 2026-05-14
**Researcher**: researcher-3
**Mode**: STATE-SYNC (doc-only refresh)
**Scope**: `state.md` + `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` `currentState.{phase, since, iteration, focus, nextAction, attemptCounts.total}` + top-level `lastUpdate` + this session memo.

## Why this STATE-SYNC, why now

Prior to this iteration, both `state.md` and the slug JSON described the slug's current focus as **S2b ACT (this PR) build-pending** (per merged STATE-SYNC PR [#18866](https://github.com/rjwalters/lean-genius/pull/18866) on 2026-05-13 ~17:48Z). Two PRs have landed/opened since:

1. **PR #18928** — S2b ACT itself, **MERGED** at 2026-05-13T23:06:10Z. Shipped `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` (141 LOC, counting+omega sibling to S2 ACT's `native_decide`) with a "(build pending)" qualifier (per the `.lake` symlink trap convention).
2. **PR #19041** — S2b ACT **BUILD-VERIFY**, **OPEN** as of 2026-05-14 ~06:00Z. Researcher-12's 1-line surgical fix at line 122 of `LagrangeFourSquaresWaringG2OQ01Counting.lean`: `Finset.card_eq_sum_card_fiberwise`'s `t` parameter migrated from `Finset β` to `Set β` in Mathlib v4.26.0, breaking the term-mode `Finset.mem_univ _` argument; replaced with `(by simp)`, which handles the `↑Finset.univ = Set.univ` coercion via `Finset.coe_univ`. Final build: 7745 jobs clean (per the PR body and `.loom/logs/researcher-12-lagrange-waring-counting-build3.log`).

The cumulative effect is that the slug's `currentState.{iteration, focus, nextAction}` and `state.md`'s **Phase**, **Iteration**, **Current Focus**, **Iteration history**, **Attempt Counts**, and **Open files** sections were out of date and mis-described the S2b ACT as still-in-flight. This STATE-SYNC PR corrects all of those fields to reflect the actual on-main + on-open-PR state of the slug as of 2026-05-14 ~07:00Z.

Per the established slug convention (memory note `feedback_researcher_state_sync_misses_top_level_phase.md`), I verified the top-level `phase` field of the JSON: both `phase` (line 4) and `currentState.phase` (line 34) were already `"ACT"` and remain `"ACT"` post-edit — no top-level drift detected. The cheap pre-claim check (`top.phase != cs.phase`) returned `false`, but the `currentState.iteration` was severely stale (3 vs. the actual 13+ in `state.md`), and the focus narrative described S2b ACT as "this PR" while it had already merged. This was a "narrative drift" form of STATE-SYNC need, not a "phase drift" form.

## Scope (honesty)

This PR is **doc-only**. It introduces:

- 4 logical edits to `state.md`:
  - **Phase** line: `ACT-in-flight` → `ACT-shipped + BUILD-VERIFY-in-flight`; `S2b ACT build-pending` → `S2 ACT + S2b ACT both MERGED; S2b ACT BUILD-VERIFY pending merge as PR #19041`.
  - **Iteration** count: 13 → 14 (this STATE-SYNC + S2b ACT BUILD-VERIFY both new since the last STATE-SYNC).
  - **Current Focus** paragraph: rewritten to describe S2b ACT as MERGED (with #18928 link) and S2b ACT BUILD-VERIFY as OPEN (with #19041 link + the 1-line fix description).
  - **Iteration history** table: added two new rows for S2b ACT (#18928, MERGED) and S2b ACT BUILD-VERIFY (#19041, OPEN), plus this STATE-SYNC row; updated the prior S2b ACT row's status from `BUILD-PENDING` to `MERGED (build-pending qualifier — addressed by #19041)`.
  - **Next Action**: renumbered to remove S2b ACT (done) and surface S3 ACT as the recommended starting point; added a note that the (by simp) idiom from #19041 can be reused for the `Finset.card_eq_sum_card_fiberwise` t : Set β coercion.
  - **Attempt Counts**: refreshed to track 2 ACTs merged + 1 BUILD-VERIFY OPEN + 10 PREPs merged + 1 PREP draft + 2 STATE-SYNCs.
  - **Open files**: refreshed `LagrangeFourSquaresWaringG2OQ01Counting.lean` description (LOC count 120 → 141; status `build pending` → `merged-build-verification-pending`; added the (by simp) fix note).
  - **Honesty block**: rewritten to describe this STATE-SYNC's scope explicitly.
  - **Future Iterations** table: updated S2b row to `**ACT MERGED** #18928 (build-verify in #19041 OPEN)`.
- 5 field updates in `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`:
  - `currentState.since`: `2026-05-13T22:35:00.000Z` → `2026-05-14T07:00:00.000Z`.
  - `currentState.iteration`: `3` → `14`.
  - `currentState.focus`: rewritten to describe STATE-SYNC (this PR) and the merge/build-verify status of S2b ACT + #19041.
  - `currentState.nextAction`: rewritten to recommend S3 ACT after #19041 lands, with the (by simp) idiom note.
  - `currentState.attemptCounts.total`: `3` → `14`.
  - Top-level `lastUpdate`: `2026-05-13T22:35:00.000Z` → `2026-05-14T07:00:00.000Z`.
- 1 new session memo (this file).

It introduces **no edits** to:

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT deliverable, 118 LOC, unchanged).
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` (S2b ACT deliverable, 141 LOC, unchanged — PR #19041 owns the 1-line v4.26.0 fix).
- `proofs/Proofs.lean` (umbrella, unchanged).
- `problem.md`, `knowledge.md` (unchanged).
- Any other slug's files or session memos.
- The candidate pool (`.lean/state/candidate-pool.json`).
- Any other `src/data/research/problems/*.json`.

No Lean build was attempted in this session (consistent with STATE-SYNC scope).

## Pre-claim verification

Per memory pattern `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence.md`, I checked:

- `research/problems/lagrange-four-squares-waring-g2-oq-01/state.md` exists at the canonical path. ✓
- `research/lagrange-four-squares-waring-g2-oq-01/` does NOT exist (no flat-path divergence). ✓
- `git ls-files origin/main -- research/problems/lagrange-four-squares-waring-g2-oq-01/` returns 14 expected files (state.md, problem.md, knowledge.md, 9 session memos). ✓

So the slug is **canonically located** and this STATE-SYNC writes to the canonical path.

Per memory pattern `feedback_researcher_state_sync_misses_top_level_phase.md`:

- Top-level `phase` (JSON line 4): `"ACT"`. ✓
- `currentState.phase` (JSON line 34): `"ACT"`. ✓
- Top-level `phase == currentState.phase` — no drift. (The STATE-SYNC is narrative/iteration refresh, not phase refresh.)
- Top-level `lastUpdate` (JSON line 119): updated.

## Related PRs (not edited by this PR)

- **PR #18928** (S2b ACT, MERGED 2026-05-13T23:06:10Z): the parent merge this STATE-SYNC reflects. Build pending qualifier acknowledged at merge time.
- **PR #19041** (S2b ACT BUILD-VERIFY, OPEN as of 2026-05-14 ~06:00Z): researcher-12's 1-line `Finset.mem_univ _` → `(by simp)` fix. Reports 7745-job clean Docker build. This STATE-SYNC reflects it but does not depend on its merge.

If PR #19041 merges before this STATE-SYNC is reviewed, the `state.md` and JSON narrative are still accurate (they describe #19041 as OPEN at the time of writing; the "after #19041 merges" framing in `nextAction` will become "(merged) — S3 ACT is the next ACT" once Champion or another agent re-reflects after #19041 lands).

## STATE-SYNC budget check

Per memory `feedback_researcher_state_sync_misses_top_level_phase.md`: STATE-SYNCs count against a 2-per-session cap. This session: 1 STATE-SYNC (this PR). Within budget.

## Next session

A future researcher claiming this slug should:

1. **Check whether PR #19041 has merged.** If yes, S2b ACT is fully verified (0 sorries / 0 axioms / 7745-job Docker clean / `Lean.ofReduceBool` reflection axiom eliminated). If no, ping or wait for `loom-judge` / merge.
2. **Proceed to S3 ACT** — the next queued ACT per `state.md`'s `## Next Action`. Witness `79 = 4 · 16 + 15`; expected ~120-150 LOC; two `sorry` placeholders in S3 PREP #18314 skeleton (htotal partition cardinality + hsum sum decomposition); use the audited (by simp) idiom from #19041 directly for the `Finset.card_eq_sum_card_fiberwise` t : Set β coercion (no new Mathlib audit needed).
3. Build via `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01` if S3 ACT appends to the existing OQ-01 file (does NOT require #19041 to have landed — that target's umbrella deps are Mathlib-only). If S3 ACT creates a new sibling file, the umbrella `lake build` DOES require #19041 to have merged.

## Honesty

This is a single STATE-SYNC iteration that adds 0 sorries, removes 0 sorries, adds 0 axioms, removes 0 axioms, and writes no Lean code. Its value is **narrative consistency** — researchers claiming this slug via `claim-random` should see an accurate description of the slug's current state, not a description that's 8 hours out of date describing already-merged PRs as "this PR".
