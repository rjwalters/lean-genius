# S8 STATE-SYNC — Post-Blocker Discharge + INFRA RED Escalation

**Date:** 2026-05-17T00:35:00Z
**Researcher:** researcher-12
**Slug:** szemeredi-full-oq-01
**Predecessor:** Session 7 (2026-05-02, PR #14878 MERGED 2026-05-02T21:18:35Z)
**Window since predecessor:** ~14 days 3 hours
**Mode:** STATE-SYNC (doc-only, 4 files, 0 Lean / gallery / lake-manifest / problem.md / knowledge.md body edits)

---

## §0. Why S8 fires

The post-ship pivot landed on a slug whose `currentState.phase: BLOCKED`
was a frozen mirror of the Session 6 (2026-04-27) snapshot. In the
14 days that followed:

1. Session 7 (PR #14878, merged 2026-05-02T21:18:35Z) discharged the
   ENTIRE blocker (6 root fixes → 35 cascading errors → file compiles).
2. The pool entry was returned to `status: available` (timing unclear;
   most likely auto-resync after the visible cascade resolution).
3. `claim-random` selected this slug back into rotation (depth-first
   tier, MODERATE+ knowledge score 35).
4. `currentState.phase` remained BLOCKED across this entire window —
   stale because no S8-class STATE-SYNC ran between #14878-merge and
   today's re-claim.

The `state.md` head (33 LOC) similarly mirrored the BLOCKED snapshot.
The `leanFiles[]` array, additionally, was structurally wrong: it
pointed only at `SzemerediFullOQ02.lean` (118 LOC, 4 thm, 0 sorry —
the sibling stub), while ALL substantive research history (Sessions 1-7,
~9 `builtItems`, the active 1 sorry + 1 axiom) targets
`FurstenbergCorrespondenceOQ01.lean` (929 LOC).

This is a strict-refinement STATE-SYNC, not deviation: the next
action documented in Session 7 was "verify Docker build of the
repaired file"; doing that requires the INFRA preconditions that are
currently absent. S8 books the discharge, escalates the new INFRA
blockers, and stages S9 to do the actual build under recovered Docker.

---

## §1. Three RED INFRA blockers (2026-05-17 host snapshot)

### §1.1 G7 — Disk floor breach

```
Filesystem      Size    Used   Avail Capacity
/dev/disk3s5   926Gi   887Gi   2.9Gi   100%
```

Same-day floor precedent (from memory):
| Slug             | Session | Disk avail at ACT-time | Disposition       |
|------------------|---------|------------------------|-------------------|
| shannon S18a-1   | #19655  | 5.8 GiB                | def-only sub-ACT  |
| ballot S78       | _other_ | 5.4 GiB                | doc-only          |
| binomial S18     | #19740  | 3.8 GiB                | doc-only (locked) |
| **this slug S8** | **PR THIS** | **2.9 GiB**        | **doc-only S8**   |

The 5.0 GiB ACT floor is a soft heuristic, not a hard threshold —
at 2.9 GiB the host will likely OOM/full-disk during a 929-LOC
Lean elaboration (peak `lake build` workload for files of this size
is ~5-10 GiB transient .lake state).

### §1.2 G8 — Docker daemon hung

```
$ docker info
[timeout; Server: section never printed]
```

This matches the post-2026-05-16T17:00Z pattern: multiple recent PRs
(abel-ruffini S7 #19755, sqrt2-minpoly S6 #19760, binomial S18
#19740) all observed `Server:` empty within the same T-2h window.
No daemon recovery action has shipped, so the condition has persisted
≥ 7 h as of this session start. Recovery requires operator
intervention (Docker Desktop restart or `colima restart` if the
backend is colima).

### §1.3 G9 — `proofs/.lake` self-symlink

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  ... .lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

A self-symlink cycle. Any `lake build` invocation that touches
`.lake` will infinite-loop or fail on `readlink`. This is a separate
recovery from G8: even if Docker comes back, the `.lake` symlink
must be removed (`rm proofs/.lake && lake update`) before any
`lake build` can succeed.

---

## §2. Discharge of the prior 35-error Mathlib blocker

Per PR #14878 commit (`9d46ff6f456` — "fix(szemeredi): repair Mathlib
API drift in FurstenbergCorrespondenceOQ01"), Session 7 fixed 6
root-cause errors that cascaded to ~35 build failures. The six fixes
are inventoried in `knowledge.md` Session 2026-05-02. As of 2026-05-17:

| Status     | Item                                                       |
|------------|------------------------------------------------------------|
| MERGED     | PR #14878 (2026-05-02T21:18:35Z)                           |
| FILE STATE | `FurstenbergCorrespondenceOQ01.lean` present at 929 LOC    |
| METRICS    | 32 thm, 8 def, 1 axiom, 3 raw sorry (1 active + 2 comment) |
| BUILD VERIFY | NOT performed in this session (G7/G8/G9 all RED)          |

The "not performed" is the key honesty calibration: I cannot say the
file builds; I can only say it is structurally well-formed and the
historic blocker description (`"35 build errors due to Mathlib v4.26
API drift"`) is no longer current. S9 must reverify.

### Sorry inventory (raw `\bsorry\b` = 3)

| Line | Context                                            | Disposition |
|------|----------------------------------------------------|-------------|
| 779  | `  sorry` — `limit_invariant_on_cylinder` body     | ACTIVE — S10 target |
| 878  | Comment: `**Remaining sorry** (1):`                | doc-string  |
| 923  | Comment: `2. One sorry for T-invariance ...`       | doc-string  |

The mechanic-canonical count is 3 (raw, no comment-strip per memory
convention); the gallery `furstenberg-correspondence-oq-01/meta.json`
`leanFile.sorries: 1` reflects the comment-stripped value (the truth
about provable sorries remaining). Both are correct under their own
convention.

---

## §3. SHA-stability spot-check (1 bearer)

Mathlib pin in `proofs/lake-manifest.json`:
```json
{
  "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
  "inputRev": "v4.26.0"
}
```

This is byte-stable since 2026-04-22 (slug `started`). All 6 Mathlib
fix targets in PR #14878 — `isOpen_discrete`, `Function.iterate_zero`,
`split_ifs`, `inferInstance` (for `CompactSpace Bool`), `congr 1`,
`omega` — were against this pin. No Mathlib bump intervened.

The remaining bearers (`ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`,
`ENNReal.Tendsto.add`, Prokhorov ingredients) were not re-walked in
this session — pin stability means a 6-bearer carry-forward is safe
under the recent SHA-stable-spot-check-not-busywork memory pattern.

---

## §4. Drift inventory (4 surfaces, all reconciled)

| Surface           | Pre-S8 value                | Post-S8 value                                    |
|-------------------|-----------------------------|--------------------------------------------------|
| state.md head     | Phase BLOCKED, Iter 4, 2026-04-27 | Phase ACT, Iter 5, 2026-05-17               |
| JSON currentState.phase | BLOCKED                | ACT                                              |
| JSON currentState.blockers | 2 stale items        | 4 items (3 INFRA RED + 1 standing CI gap)        |
| JSON leanFiles[]  | 1 entry (wrong file)        | 2 entries (correct sibling + actual subject)     |
| Registry phase    | OBSERVE                     | ACT                                              |
| Registry lastUpdate | 2026-04-24                | 2026-05-17                                       |
| JSON lastUpdate   | 2026-04-27                  | 2026-05-17                                       |

`knowledge.md` body is NOT touched in this session — the Session 7
entry is already a faithful record of #14878 work, and re-writing
prior sessions is anti-pattern. A future S9 may add a Session 8
epilogue if build-verify produces new findings.

`problem.md`, `selection-report.md`, `literature/` are untouched.

---

## §5. S9 picker decision matrix

| Condition                                            | Action                                    |
|-----------------------------------------------------|-------------------------------------------|
| Docker recovers AND disk ≥ 5 GiB                    | S9 build-verify under recovered Docker    |
| Docker recovers, disk < 5 GiB                       | S9 build-verify under sandboxed temp dir  |
| Docker still hung, ≤ 4h since this STATE-SYNC       | Hold; another agent / mechanic may absorb |
| Docker still hung, > 4h, no intervening drift       | S9 graceful exit (no-op; await INFRA fix) |
| Docker still hung, > 4h, intervening drift          | S9 STATE-SYNC absorbing new drift only    |
| Build succeeds                                      | S10 PREP: activate limit_invariant_on_cylinder (60-LOC structure documented in-file @ line ~760) |
| Build fails with new errors                         | S9b diagnostic — likely Mathlib advance, return slug to BLOCKED with fresh inventory |

INFRA recovery script (for S9 operator or daemon):

```bash
# 1. Free disk
docker system prune -af --volumes  # if Docker recovers first
rm -rf ~/Library/Caches/lake-packages/* 2>/dev/null
git -C /Users/rwalters/GitHub/lean-genius gc --aggressive --prune=now

# 2. Fix .lake symlink
rm /Users/rwalters/GitHub/lean-genius/proofs/.lake
cd /Users/rwalters/GitHub/lean-genius/proofs && lake update

# 3. Restart Docker (operator action)
# - Docker Desktop: Quit + reopen
# - colima: colima stop && colima start

# 4. Verify
docker info | grep "Server Version"
df -h / | tail -1
ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake  # should NOT be self-symlink
```

---

## §6. Explicit non-actions (anti-overreach)

- **No `.lean` file edits.** `FurstenbergCorrespondenceOQ01.lean` is
  left at 929 LOC byte-for-byte. The active sorry @ 779 is the S10
  target, not the S8 target.
- **No `pnpm build`.** Skip per memory entry — would regenerate ALL
  research JSONs via `research:enrich`, conflicts with this targeted
  fix, and would leak untracked JSONs for new slugs.
- **No gallery meta edits.** `src/data/proofs/furstenberg-correspondence-oq-01/meta.json`
  is already in sync with the actual file (`leanFile.lineCount: 929`,
  `theoremCount: 32`, `definitionCount: 9`, `axiomCount: 1`,
  `sorries: 1` — comment-stripped convention). The gallery uses a
  different counting convention from the research-JSON leanFiles[],
  and both are correct under their own conventions.
- **No `lake-manifest.json` edit.** Mathlib pin is byte-stable since
  2026-04-22.
- **No `problem.md`, `selection-report.md`, `knowledge.md` body
  edits.** Only `state.md` (4-line head + iteration-log prepend)
  and the canonical JSON's `knowledge.{progressSummary,nextSteps}`
  fields (in-place edits, not body rewrites).
- **No sibling-slug edits.** `szemeredi-full`, `szemeredi-full-oq-02`,
  and other Szemerédi family entries are not in scope.
- **No `proofs/.lake` symlink fix in this PR.** Recovery requires
  operator action (see §5); shipping a fix in a doc-only PR would
  mix infrastructure repair with state tracking.
- **No build attempt.** Docker is hung; even if I tried, it would
  add no signal and might destabilize a running daemon recovery.

---

## §7. Honesty calibration

What I know for certain (verified in this session):
- PR #14878 is MERGED (gh api confirmed mergedAt 2026-05-02T21:18:35Z).
- `FurstenbergCorrespondenceOQ01.lean` exists at 929 LOC with 1
  active sorry + 1 axiom + 32 theorems + 8 defs.
- Mathlib pin `2df2f0150c…` matches the pin Session 7 used.
- Host has 2.9 GiB disk avail, Docker hung, `.lake` self-symlinked.

What I have NOT verified in this session:
- Whether `FurstenbergCorrespondenceOQ01.lean` actually builds at the
  current Mathlib pin. Session 7's claim is plausible (6 root fixes
  → cascade should clear) but unverified locally.
- Whether the 60-LOC `limit_invariant_on_cylinder` proof structure
  in the file comment is still type-correct (uses Portmanteau API
  that may have shifted).
- Whether the local `seqCompact_probabilityMeasure_cantor` axiom is
  still the minimal Prokhorov gap (Mathlib v4.26 may have shipped
  Prokhorov in the interim — needs re-survey).

These verifications are S9 / S10 work, not S8.

---

## §8. Memory citations

This session pattern most closely matches:
- `_long_completed_slug_with_research_json_stale_while_statemd_gallery_lean_all_canonical_inverse_of_statemd_drift`
  — INVERSE in the sense that state.md *was* drifted here (not just
  JSON); shares the 3-file + 15-field reconcile shape.
- `_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_due_to_historic_build_pending_chain_but_3_red_infra_blockers_post_merge_with_mechanic_partial_discharge`
  — shares the 3-RED-INFRA blocker shape (G7/G8/G9) and the
  build-pending-qualifier strategy.
- `_postship_pivot_to_act_ready_slug_with_predecessor_prep_escalation_and_single_disk_degradation_delta_across_sameday_softfloor_ship_thin_statesync`
  — shares the disk-floor cross-precedent reasoning.

This is NOT a fit for:
- `_long_completed_slug_with_research_json_stale_while_statemd_gallery_lean_all_canonical`
  — slug is NOT completed; it is active research with 1 active sorry.
- `_claim_random_lands_on_long_completed_slug_due_to_registry_json_phase_observe_status_active_drift`
  — slug is NOT completed; the registry-phase mismatch here is
  OBSERVE → ACT, not OBSERVE → DONE.

---

## §9. Files in this PR

1. `research/problems/szemeredi-full-oq-01/state.md` — head rewrite +
   iteration-log seed (~80 LOC up, 33 LOC out).
2. `src/data/research/problems/szemeredi-full-oq-01.json` — 14-field
   surgical edit: `currentState.{phase, since, iteration, focus,
   blockers, nextAction, attemptCounts}` (7 fields) + `knowledge.
   {progressSummary, insights[+1], mathlibGaps[-1], nextSteps}`
   (4 fields) + `lastUpdate` + `leanFiles[0].lineCount` +
   `leanFiles[+1]` (FurstenbergCorrespondenceOQ01 entry).
3. `research/registry.json` — 2-field edit (phase OBSERVE → ACT,
   lastUpdate 2026-04-24 → 2026-05-17).
4. `research/problems/szemeredi-full-oq-01/sessions/2026-05-17-s08-statesync-postblocker-discharge.md`
   — this memo (NEW, ~290 LOC, 9 sections).

Total: 4 files, ~+380/-30 LOC, all doc/JSON, 0 Lean changes.
