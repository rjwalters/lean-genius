# S4 precheck — parent-file blocker found (Mathlib v4.26.0 regression)

**Researcher**: researcher-9
**Date**: 2026-05-14
**Phase**: ACT (precheck only — doc-only, no Lean delta; **parent-file blocker** found, NOT my fix to make in research scope)
**Iteration**: 9 (S3 SCAFFOLD was iteration 3; 5 S4 OBSERVE/PREP PRs in iterations 4-8)
**Predecessor PRs**:
- #18000 (S1 OBSERVE, MERGED) — n×n scaffold map
- #18098 (S2 ACT, MERGED) — Route A `qdetF` over a field
- #18214 (S3 SCAFFOLD, MERGED, "build pending") — Route B `qdetN_step` + sorried `qdetN_step_eq_qdetF`
- #18346 (S4 OBSERVE, MERGED) — Minv-construction fork + S6 Cramer path
- #18409 (S4 PREP, MERGED) — block-Schur reshape + sign-discrepancy
- #18525 (S4c PREP, MERGED) — n=2 sign-quadrant verification
- #18563 (S4d PREP, MERGED) — direct adjugate path
- #18751 (S4e PREP, MERGED) — `det_eq_sum_mul_adjugate_row` alternative + line-drift audit

## Headline (two-line summary)

Pre-claim Docker build per MEMORY.md `feedback_researcher_docs_only_chain_silent_parent_regression` (4+ consecutive doc-only PREP PRs trigger) **fails** on origin/main: 14 errors in `Proofs/CramersRuleOQ01OQ02.lean` (parent of S2's Route A) + 13 errors in `Proofs/CramersRuleOQ01OQ02OQ01.lean` (parent of S3's Route B) = **27 errors total, all in untouched parent files**. The slug's own `Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` never gets compiled because the parent chain blocks elaboration; its build status is **unknown** under v4.26.0. This is doctor/mechanic-scope work; per MEMORY.md `feedback_researcher_parent_file_repair_fix_and_rebuild_loop`, the listed 27 errors are a **lower bound** (Lean halts at first error per file). The S3 SCAFFOLD's "Build pending — worktree `.lake` symlink" qualifier was a false-alarm precedent that masked this real regression for ~2 days through 5 S4 PREP/OBSERVE sessions.

## §1. Build evidence

Command (from worktree CWD, per MEMORY warning on `docker-build.sh` mount target):
```
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9
./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01
```

Result (`.loom/logs/researcher-9-cramers-s4-precheck.log`): `Build failed with exit code 1` after Mathlib v4.26.0 cache hit. Parent-file errors precede the slug's own file in dependency order; the slug file never gets a chance to be elaborated.

## §2. Full error inventory (27 lines)

### `Proofs/CramersRuleOQ01OQ02.lean` (14 errors, parent of S2 Route A)

| Line:Col | Error class | Mathlib-API hypothesis |
|---|---|---|
| 118:33 | unsolved goals | tactic broken by v4.26.0 normalization shift |
| 157:19 | Ambiguous term | likely namespace collision (e.g. `det_fin_three`) |
| 162:19 | Ambiguous term | same pattern |
| 184:37 | unsolved goals | tactic broken |
| 283:42 | unsolved goals | tactic broken |
| 287:17 | rewrite failed | pattern lemma renamed/rephrased |
| 344:60 | unsolved goals | tactic broken |
| 348:60 | unsolved goals | tactic broken |
| 363:54 | rewrite failed | pattern lemma renamed |
| 374:46 | rewrite failed | pattern lemma renamed |
| 417:19 | Ambiguous term | namespace collision |
| 422:19 | Ambiguous term | namespace collision |
| 448:36 | unsolved goals | tactic broken |
| 450:36 | Application type mismatch | API signature change |

### `Proofs/CramersRuleOQ01OQ02OQ01.lean` (13 errors, parent of S3 Route B)

| Line:Col | Error class | Mathlib-API hypothesis |
|---|---|---|
| 76:4 | failed to synthesize `CommRing D` (under `[DivisionRing D]`) | typeclass tightening — some det/adjugate lemma now requires `CommRing` where it accepted `DivisionRing` before |
| 76:58 | unsolved goals | dependent on 76:4 |
| 81:4 | failed to synthesize `CommRing D` | same |
| 81:58 | unsolved goals | dependent |
| 86:4 | failed to synthesize `CommRing D` | same |
| 86:58 | unsolved goals | dependent |
| 120:61 | unsolved goals | tactic broken |
| 125:61 | unsolved goals | same |
| 130:61 | unsolved goals | same |
| 156:72 | unsolved goals | tactic broken |
| 241:35 | unsolved goals | tactic broken |
| 249:49 | unsolved goals (goal: `A 1 1 * A 2 2 - A 1 2 * A 2 1 = (block3 A 0 0).det`) | `simp [block3_00_det]` no longer unifies; linter says "unused" |
| 273:52 | rewrite failed: pattern `?m.69⁻¹ * ?m.69` in `(A.det⁻¹ * A.det) • b = b` | **`inv_mul_cancel` family v4.26.0 refactor** — likely group/groupWithZero refinement to `inv_mul_cancel₀` |

## §3. Mathlib v4.26.0 regression classification

The 27 errors cluster into ~4 regression classes:

1. **`inv_mul_cancel` family v4.26.0 refactor (line 273 + ~5 others)** — `(x⁻¹ * x)` pattern no longer matches `inv_mul_cancel` directly. Per MEMORY.md general Mathlib drift pattern (cf. `feedback_researcher_mathlib_v426_dvd_sub_term_mode_motive_kit`), Mathlib v4.26.0 has been splitting `Group` ↔ `GroupWithZero` lemmas; the canonical name is likely `inv_mul_cancel₀ : a ≠ 0 → a⁻¹ * a = 1`.

2. **Typeclass tightening (`CommRing D` required under `DivisionRing D`, lines 76/81/86)** — `Matrix.det` for 3×3 likely lost the `DivisionRing` route; needs `CommRing` for `block3_*_det` lemmas.

3. **`Ambiguous term` (lines 157, 162, 417, 422 in OQ02 parent)** — Mathlib v4.26.0 likely promoted a local `det_fin_three` or similar to root namespace, creating a conflict with the parent file's local definition. Fix: `Matrix.det_fin_three` (or whichever the canonical name is).

4. **Tactic-normalization shifts (many `unsolved goals`)** — `simp` / `ring` / `nlinarith` calls that previously closed goals now leave residue; consistent with MEMORY entries on v4.26.0 elaborator strictness (cf. `feedback_researcher_mathlib_v426_dvd_sub_term_mode_motive_kit`, `feedback_researcher_mathlib_v426_tactic_gotchas_kit`).

## §4. Scope decision — doc-only STATE-SYNC, NOT research repair

Per MEMORY.md `feedback_researcher_parent_file_blocker_standalone_extract_verification` and `feedback_researcher_parent_file_build_unblocker_inpr_pattern`:

- **In-PR one-line unblocker** is appropriate when fix is demonstrably ≤ 3 LOC + correct (e.g. one `linarith → calc` chain, one rename). **NOT here**: 27 errors across 2 files, multiple regression classes.
- **Separate fix-PR** is appropriate for small repair bundles. Here, the repair is multi-class (typeclass + lemma-rename + namespace + tactic-shift) and crosses ~4-5 distinct Mathlib API drifts. Estimated repair LOC: ~40-70 (~2-3 LOC per error).
- **doctor/mechanic-scope** — this is the right fit. The mechanic agent specializes in cross-cutting Mathlib drift repair on parent files; researchers should not bundle this into a research PR.

This PR ships **doc-only**:
- The full error inventory (this session log) for the next mechanic to pick up
- State.md and JSON refreshed to reflect the 5 merged S4 PREP/OBSERVE PRs (currently stale at S3 SCAFFOLD, iteration 3, lastUpdate 2026-05-12T08:30Z — 2 days stale)
- Replace the S3 SCAFFOLD "Build pending — worktree `.lake` symlink" false-alarm qualifier with a HONEST "PARENT-FILE BLOCKER" status

## §5. What this PR changes

Doc-only, no Lean delta. Three file changes:

1. **`research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/state.md`** — refresh to acknowledge merged S4 PREP/OBSERVE chain + raise the parent-file blocker:
   - Phase: `ACT (S3 SCAFFOLD)` → `ACT (S4 PREP saturated; parent-file blocker)`
   - Iteration: 3 → 9
   - Since: 2026-05-12T12:30:00Z → 2026-05-14T11:09:00Z
   - Current Focus: rewrite to reflect S4 PREP chain conclusions + raise the parent-file blocker as the priority next-action (mechanic-scope)
   - Add Session 4–8 summaries (S4 OBSERVE through S4e PREP)
   - Replace S3 SCAFFOLD "Build status: Build pending — worktree `.lake` symlink trap" with HONEST status: "Build status (verified 2026-05-14 via Docker): UNKNOWN for this file (parents fail to compile under Mathlib v4.26.0; see Blockers/Mathlib regression)."

2. **`src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`** — refresh `currentState`:
   - `iteration`: 3 → 9
   - `since`: 2026-05-12T12:30:00Z → 2026-05-14T11:09:00Z
   - `lastUpdate`: 2026-05-12T08:30:00Z → 2026-05-14T11:09:00Z
   - `focus`: rewrite to reflect parent-file blocker + S4 PREP chain saturation
   - `blockers`: prepend parent-file blocker as `blockers[0]`; replace S3-era ".lake symlink" operational blocker with HONEST parent-file blocker
   - `attemptCounts.total`: 1 → 6

3. **`research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-14-s4-precheck-parent-file-blocker.md`** — this session log (new file).

## §6. Recommendation for next session

**Priority: doctor or mechanic agent.** The 27-error parent-file repair is the gating blocker for ALL forward progress on this slug. S4 ACT (closing the `qdetN_step_eq_qdetF` sorry per the synthesized PREP spec) is meaningless until parents build. Suggested PR title for the repair: `fix(cramers-rule-oq-01-oq-02 + -oq-01): Mathlib v4.26.0 regression repair (27 errors in parents, doctor-scope)`.

**Alternative — coordinated research+mechanic:** Issue a Loom issue with the full inventory above, assign to a mechanic via `loom:issue` label, and once it's closed, S4 ACT can land. ETA: ~1-2 mechanic sessions of focused work given the multi-class drift.

**Do NOT attempt S4 ACT until parents build.** Per MEMORY.md `feedback_researcher_parent_file_repair_fix_and_rebuild_loop`, the 27-error count is a lower bound — once class-1 (the `inv_mul_cancel` rewrite family) fixes land, additional errors may surface in `Proofs/CramersRuleOQ01OQ02OQ01.lean` (Lean halts at first error per file).
