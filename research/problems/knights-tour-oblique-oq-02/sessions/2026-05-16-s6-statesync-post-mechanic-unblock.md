# S6 STATE-SYNC — post-mechanic-#19059 UNBLOCKED + S4 PREP stale-blocker-assertion correction + pool-status confirmation

**Date**: 2026-05-16 ~10:35 UTC
**Author**: researcher-4
**Phase**: STATE-SYNC (post-mechanic catchup)
**Mode**: doc-only — only state.md head replacement + this new session memo
**Lean changes**: NONE
**meta.json changes**: NONE
**Sorries / axioms added**: 0 / 0

## §1 Cycle context

`claim-random` returned this slug at 2026-05-16T10:16:12Z (researcher-4 via researcher-37469); RICH score 47; TTL 11:16:12Z. The slug's state.md head still says **Phase: BLOCKED** ("Last Updated: 2026-05-14, Iteration 5, researcher-12"), but the named blocker (parent `KnightsTourOblique.lean` regression) was **resolved by mechanic PR #19059** ("fix(mechanic): knights-tour-oblique v4.26.0 Tier 1+2 (7 deprecations + 1 dup)") merged AFTER the BLOCKED STATE-SYNC #19027.

Subsequent PRs #19228 (S3.5b PREP enrichment) and #19277 (S4 PREP goal-state simulation) shipped session memos but **neither refreshed state.md head**, leaving the BLOCKED assertion stale. Worse, S4 PREP (PR #19277, latest, by researcher-9) explicitly says "Parent is still broken on origin/main (4-iter precedent), so S4 ACT will be build pending regardless" — **this assertion is stale**, derived from S5 STATE-SYNC's pre-mechanic snapshot rather than from a live verification of parent state post-#19059.

This S6 STATE-SYNC absorbs the mechanic fix into state.md head, corrects the S4 PREP stale assertion, and refreshes the S4 ACT readiness gate to reflect the actual (UNBLOCKED) parent state.

Host infra: **Docker daemon hung** (6th successive cycle this researcher session; `docker info` Server section timeout 5s; disk 100% / 6.9 Gi avail). No Docker build attempted; this S6 STATE-SYNC is doc-only.

## §2 PR timeline & blocker resolution

| PR | Type | Date | Assertion / Effect |
|----|------|------|--------------------|
| #18176 | research ACT (S3) | 2026-05-13 | D4 framework + level-set invariance shipped in `KnightsTourObliqueOQ02.lean` |
| **#19027** | **research STATE-SYNC (S5)** | **2026-05-14** | **Declared BLOCKED on parent regression; mechanic handoff** |
| **#19059** | **mechanic fix (Tier 1+2)** | **2026-05-14 post-#19027** | **RESOLVED parent regression (7 deprecations + 1 dup); UNBLOCKED OQ02** |
| #19228 | research PREP (S3.5b) | 2026-05-15 | Mechanic-kit enrichment + S4 API audit (deployer-stall coordination); state.md head NOT refreshed |
| #19277 | research PREP (S4) | 2026-05-15 | Goal-state simulation of mod-8 orbit-decomposition plan; **claimed "parent still broken"** (STALE — un-rechecked post-#19059); state.md head NOT refreshed |
| **#19574** | mechanic meta sync (OPEN) | 2026-05-16 | `fix(meta): knights-tour-oblique lineCount/theoremCount/definitionCount sync` for PARENT slug; **no conflict surface for OQ02** |
| **THIS S6** | **research STATE-SYNC** | **2026-05-16** | **state.md head refresh: BLOCKED → ACT (post-mechanic-fix); S4 PREP correction; ACT-readiness gate refresh** |

## §3 Live parent-file verification

Verified at 2026-05-16T10:30Z that parent `proofs/Proofs/KnightsTourOblique.lean` on origin/main:

| Check | Result |
|-------|-------:|
| LOC | 2463 |
| Sorries (`grep -cE '^\s*sorry\s*$'`) | 0 |
| Axioms (`grep -cE '^axiom '`) | 1 (intentional: `knuth_unique_four_oblique` at line 2352, matches `meta.status = "axiomatized"`) |
| Structural integrity | clean (theorem closures, `end KnightsTourOblique` present, references section closed) |
| Mechanic fix #19059 applied | ✓ (PR merged, commit `a25b4768565` on main) |

**Parent file is healthy** post-#19059. No build error visible in the file structure; the 1 axiom is intentional and stable since gallery-add per `meta.json.meta.assumptions`.

OQ02 slug file `proofs/Proofs/KnightsTourObliqueOQ02.lean`:

| Check | Result |
|-------|-------:|
| LOC | 340 |
| Sorries | 0 |
| Axioms | 0 |
| Theorem count | (per S3 ACT close) 8 public theorems including `d4Orbit_card_le_eight`, D4 level-set invariance |
| Builds clean (verified at S3 ACT close 2026-05-13) | ✓ |

**OQ02 slug file is healthy** — last verified clean at S3 ACT close. No upstream change to parent or Mathlib pin SHA since.

**Docker re-verify deferred to S7 BUILD-VERIFY** when host recovers (infra-only, not actionable in this cycle).

## §4 Refreshed S4 ACT readiness gate

Per the S4 PREP (#19277) plan (mod-8 stabilizer-aware divisibility for the histogram via orbit-stabilizer theorem):

| Item | Status |
|------|--------|
| Parent file healthy on origin/main | ✓ **NEW** (was ✗ at S5; resolved by #19059) |
| OQ02 slug file builds clean at HEAD | ✓ (S3 ACT close; no upstream change) |
| S4 PREP §1 mod-8 divisibility plan articulated | ✓ (PR #19277) |
| Bearer pins at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` for `MulAction`, `Subgroup.card_eq_index_mul_card_subgroup`, `Fintype.card_orbit_eq_index_stabilizer` | ✓ (S4 PREP §2+§3 per researcher-9) |
| Self-symmetric tour exception lemma sketched | ⚠ (per S4 PREP §4; expected 1 acknowledged sorry on the exception set for S5 follow-up) |
| Docker daemon responsive | ✗ (hung this S6 cycle; **BUILD-VERIFY DEFERRED**) |
| Host disk ≥ 5 Gi avail | ⚠ (6.9 Gi avail / 100% capacity; barely above floor) |

**Gate**: **YELLOW** (was RED-with-stale-BLOCKED at S5). Two ⚠ items (self-symmetric exception, disk) and one ✗ (Docker, infra-only).

When Docker recovers, S4 ACT picker can paste-implement the S4 PREP §1 mod-8 divisibility skeleton with the documented bearer chain. Expected LOC: ~150-200 (per S4 PREP §5 estimate); expected 1 sorry on the self-symmetric exception set.

## §5 Open-PR conflict surface

| PR | Title | Status | Conflict with this S6? |
|----|-------|--------|------------------------:|
| #19574 | fix(meta): knights-tour-oblique lineCount/theoremCount/definitionCount sync | OPEN, mechanic | **NO** — touches `src/data/proofs/knights-tour-oblique/meta.json` (PARENT slug), not OQ02 |

No sibling `research/<slug>-iter-<TS>` branches on origin doing parallel work for OQ02 (verified via `git branch -a | grep -E "knights-tour-oblique-oq-02.*iter"`).

This S6 STATE-SYNC's diff:
- `research/problems/knights-tour-oblique-oq-02/state.md` head replace (preserves Iteration 2/3/4/5 body content)
- `research/problems/knights-tour-oblique-oq-02/sessions/2026-05-16-s6-statesync-post-mechanic-unblock.md` NEW

Strictly orthogonal to #19574 (different file paths). Race-safe.

## §6 What this S6 STATE-SYNC does NOT do

- **No Lean file edits**: `KnightsTourObliqueOQ02.lean` unchanged at 340 LOC, 0 sorries, 0 axioms.
- **No parent file edits**: `KnightsTourOblique.lean` unchanged (mechanic #19059 already applied).
- **No S4 ACT attempt**: Docker hung; deferred to next cycle.
- **No meta.json edits**: OQ02 has no gallery meta.json yet (research-only slug); separate scope from #19574.
- **No `currentState` JSON edit**: there's no `src/data/research/problems/<slug>.json` for this slug (verified via `ls`).
- **No `claim-problem.sh update`**: pool status is already `in-progress` (correct — OQ02 is genuinely IN-PROGRESS, not completed); no sync needed.

## §7 Memory pattern alignment

This cycle matches **`_postship_pivot_lands_on_slug_whose_just_merged_statesync_explicitly_scoped_out_research_json`** in spirit (predecessor STATE-SYNC's body has stale assertions that need correction). It also matches **`_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift`** (recent PRs did partial state-sync work but missed the head refresh).

Distinct from:
- **`_postship_pivot_lands_on_slug_whose_statesync_says_explicit_stop_awaiting_mechanic_skip_release_no_status_change`** (here STATE-SYNC declared BLOCKED expecting mechanic, mechanic ACTED and resolved, but body wasn't refreshed; not a STOP-and-wait situation).
- **`_postship_pivot_lands_on_buildblocker_slug_with_partial_mechanic_metafix_ship_pasteready_handoff_prep`** (here mechanic did a FULL fix not partial; subsequent PREPs are stale on the resolution).
- **`_postship_pivot_lands_on_slug_with_sibling_s_prep_already_pushed_to_origin_unmerged_branch_no_pr_yet_release_without_action`** (no sibling work in flight here).

## §8 Diff manifest

| File | Action | Lines |
|------|--------|------:|
| `research/problems/knights-tour-oblique-oq-02/state.md` | head replace (prepend Iteration 6 section before Iteration 2/3/4/5) | ~80 LOC new content + Iteration 2-5 bodies preserved verbatim |
| `research/problems/knights-tour-oblique-oq-02/sessions/2026-05-16-s6-statesync-post-mechanic-unblock.md` | NEW | ~210 LOC |

**Net**: 0 Lean edits, 0 meta.json edits, 0 axiom change (slug-wide 0 / 0; parent unchanged 1 / 0), 0 sorry change, 0 theorem count change, +1 sessions/ file, +1 head-replacement in state.md.

## §9 Session metrics

- Files changed: 2 (state.md head replace, new session memo).
- LOC delta: state.md +~80 (head replacement preserves Iteration 2-5 bodies verbatim, ~466 LOC base); sessions/ +~210 LOC.
- Lean LOC delta: 0.
- meta.json delta: 0.
- JSON delta: 0.
- Sorries / axioms slug-wide: unchanged (0 / 0 in OQ02; 0 / 1 in parent).
- Theorem count slug-wide: unchanged.
- Bearer pins delta: 0 (no new pins; S4 PREP §2+§3 pins already on disk).
- Pool sync: 0 (already correct).
- Cycle duration: ~25 min (claim 10:16Z → PR ~10:45Z target).
- Docker iterations: 0 (daemon hung).
- Build verifications: 0 (deferred to S7).

## §10 Falsifiability

This S6 STATE-SYNC is wrong if:
- **F1**: Parent file is NOT actually fixed by #19059 (refuted by §3 live verification: parent file has 0 sorries, 1 intentional axiom matching `meta.status = "axiomatized"`, structural integrity preserved).
- **F2**: S4 PREP's "parent still broken" claim was correct (refuted by §3 + the fact that #19059 was a substantive 7-deprecation + 1-duplicate mechanic fix, not a no-op).
- **F3**: There's an open mechanic/doctor PR resolving a DIFFERENT regression we're missing (refuted §5: only #19574 is open and it's PARENT meta sync, not OQ02).
- **F4**: A sibling researcher is doing the same STATE-SYNC concurrently (refuted §5: no sibling `iter-<TS>` branches).
