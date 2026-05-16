# S13 STATE-SYNC — Research-JSON Catchup Post-S12 Verified Confirmation

**Date**: 2026-05-15
**Researcher**: researcher-12
**Phase**: S13 STATE-SYNC (doc-only; closes research-JSON drift left by S12)
**Depends on**:
- PR #19078 (S8 BUILD-VERIFY 7-error inventory, MERGED 2026-05-15T23:26:37Z)
- PR #19220 (S9 PREP mechanic kit, MERGED 2026-05-15T18:05:33Z)
- PR #19298 (S10 PREP audit, MERGED 2026-05-15T18:00:47Z)
- PR #19303 (S11 PREP ACT-readiness gate, MERGED 2026-05-15T19:00:33Z)
- PR #19101 (S9 ACT mechanic fix, MERGED 2026-05-15T22:59:15Z, commit `be08fef58bb`)
- PR #19334 (S12 STATE-SYNC build-verified confirmation, MERGED 2026-05-15)

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
unchanged from S11 PREP / S12 STATE-SYNC; verified via
`proofs/lake-manifest.json`).

**Base commit**: `cf1cfa085e42ac65894740a787228d22cc2f269e` (current
`origin/main` HEAD at S13 write time).

## 1. Purpose

S12 STATE-SYNC (PR #19334) consumed the merged S8 → S9 PREP → S10
PREP → S11 PREP → S9 ACT cascade and updated `state.md` + `meta.json`
+ added a 271-LOC build-verified confirmation session memo. Its §10
"Conflict-free guarantees" manifest **explicitly scoped** the PR to:

> - `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s12-state-sync-build-verified.md` (new file, this note)
> - `research/problems/ehrhart-cube-proven-oq-04/state.md` (phase + next-action rewrite, body preserved)
> - `src/data/proofs/ehrhart-cube-proven-oq-04/meta.json` (4 field updates: status, badge, lineCount, theoremCount + description trim)

The `src/data/research/problems/ehrhart-cube-proven-oq-04.json`
file (different path — under `src/data/research/problems/`, not
`src/data/proofs/`) was **deliberately excluded** from S12's scope.
At S13 claim time (2026-05-15T~23:30Z), this research-JSON file
remained at its S7 snapshot (PR #18939, 2026-05-13), showing:

- top-level `phase: "SCAFFOLDED"` (truth: `"VERIFIED"`)
- `currentState.phase: "PROVED"` (truth: `"VERIFIED"`)
- `currentState.since: "2026-05-13T23:00:00Z"` (truth: `"2026-05-15T22:59:15Z"`)
- `currentState.iteration: 7` (truth: 13 with S13)
- `currentState.focus`: S7 POLYNOMIAL-COROLLARIES narrative (truth: post-verified)
- `currentState.nextAction`: "S8+ (optional): (1) verify the full-file Docker build…" (truth: S8 done, build verified, S14+ optional)
- `currentState.attemptCounts.total: 7` (truth: 13)
- `currentState.attemptCounts.approachesTried: 0` (truth: 2 — S8 inventory + S9 ACT mechanic)
- `knowledge.progressSummary`: S7 (build pending) narrative (truth: S12 BUILD-VERIFIED)
- `knowledge.builtItems`: missing S8-S13 entries (S8 inventory, S9 PREP, S10 PREP, S11 PREP, S9 ACT, S12 STATE-SYNC, S13 STATE-SYNC)
- `knowledge.insights`: missing 3 post-S8 insights (latent-defect interpretation, zero-drift cascade pedagogy, v4.26.0 no-op rewrite trap)
- `knowledge.nextSteps`: 4 stale items targeting S5/S5/S6/S7+ (all done) — replaced by S14/S15/S16/S17 forward plan
- `lastUpdate: "2026-05-13T23:00:00Z"` (truth: 2026-05-15)
- `leanFiles[1].lineCount: 772` (truth: 775, `wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean`)

This S13 STATE-SYNC closes the drift in **one** doc-only PR touching
exactly three files (research-JSON + state.md head + this new
session memo). No Lean source edits, no `meta.json` edits, no
sibling-session edits, no parent-file edits.

## 2. Per-field drift table (pre-S13 → post-S13)

| Path | Pre-S13 value | Post-S13 value | Source of truth |
|---|---|---|---|
| `.phase` | `"SCAFFOLDED"` | `"VERIFIED"` | state.md L3 phase |
| `.status` | `"active"` | `"active"` (unchanged) | claim-script convention |
| `.currentState.phase` | `"PROVED"` | `"VERIFIED"` | state.md L3 + meta.json `status: verified` |
| `.currentState.since` | `"2026-05-13T23:00:00Z"` | `"2026-05-15T22:59:15Z"` | state.md L4 (S9 ACT merge timestamp) |
| `.currentState.iteration` | `7` | `13` | state.md L5 (S13 STATE-SYNC) |
| `.currentState.focus` | S7 POLYNOMIAL-COROLLARIES narrative | S13 STATE-SYNC narrative w/ 12-item drift list | state.md current focus block |
| `.currentState.nextAction` | "S8+ (optional)…" | "S14 (Mathlib upstream) / S15 (regression check)…" | state.md "Next Action" |
| `.currentState.attemptCounts.total` | `7` | `13` | state.md attempt-counts §  |
| `.currentState.attemptCounts.approachesTried` | `0` | `2` | state.md attempt-counts § |
| `.knowledge.progressSummary` | S7 build-pending narrative | S12 BUILD-VERIFIED v4.26.0 narrative | state.md "What's Built" + meta.json `status: verified` |
| `.knowledge.builtItems` | 19 entries (through S7) | 26 entries (+S8 inventory, S9 PREP, S10 PREP, S11 PREP, S9 ACT, S12 STATE-SYNC, S13 STATE-SYNC) | git log + state.md "What's Built" |
| `.knowledge.insights` | 10 entries | 13 entries (+ latent-defect interpretation, +zero-drift cascade pedagogy, +v4.26.0 no-op rewrite trap) | post-S8 observations |
| `.knowledge.nextSteps` | 4 stale items (S5/S5/S6/S7+) | 4 forward items (S14/S15/S16/S17) | state.md "Next Action" |
| `.lastUpdate` | `"2026-05-13T23:00:00Z"` | `"2026-05-15T23:30:00Z"` | this PR write timestamp |
| `.leanFiles[1].lineCount` | `772` | `775` | `wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean` |
| `.leanFiles[1].theoremCount` | `30` | `30` (unchanged) | meta.json `theoremCount: 30` (matches) |
| `.leanFiles[1].axiomCount` | `0` | `0` (unchanged) | `grep -c "^axiom " ... = 0` |
| `.leanFiles[1].sorryCount` | `0` | `0` (unchanged) | source-level sorry-free (2 `sorry` matches in file are in comments) |
| `.leanFiles[1].defCount` | `2` | `2` (unchanged) | `eulerianNumber` + `cubeHStarPoly` |

**Total**: 12 fields updated, 5 fields confirmed unchanged.

## 3. Source-of-truth audit walkthrough

### Lean file (must match `meta.json.leanFile.lineCount` = 775)

```
$ wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean
     775 proofs/Proofs/EhrhartCubeProvenOQ04.lean

$ grep -c "^axiom " proofs/Proofs/EhrhartCubeProvenOQ04.lean
0

$ grep -n "sorry" proofs/Proofs/EhrhartCubeProvenOQ04.lean
15:  remaining sorry `eulerian_palindrome` (A(d,k) = A(d,d-1-k) for k<d) by
66:  Concrete (proven, no sorry):
# Both matches are inside docstring comments — Lean source is sorry-free.

$ grep -c "^def\|^noncomputable def" proofs/Proofs/EhrhartCubeProvenOQ04.lean
2

# Public theorems (theorem/lemma, excluding examples):
$ grep -c "^theorem\|^lemma\|^protected theorem\|^protected lemma" proofs/Proofs/EhrhartCubeProvenOQ04.lean
30
```

### state.md (line 5: `**Iteration**: 12` pre-S13)

```
$ head -7 research/problems/ehrhart-cube-proven-oq-04/state.md
# Current State

**Phase**: VERIFIED (S9 ACT mechanic fix PR #19101 merged 2026-05-15T22:59:15Z; Docker build clean, 7743 jobs; S12 STATE-SYNC absorbs the S8 → S9 PREP → S10 PREP → S11 PREP → S9 ACT cascade)
**Since**: 2026-05-15T22:59:15Z (S9 ACT mechanic fix merge — first clean Docker baseline)
**Iteration**: 12
**Researcher**: researcher-12 (S12 STATE-SYNC)
```

state.md head is the canonical phase/since/iteration record per the
gallery convention. S13 STATE-SYNC bumps `Iteration: 12 → 13` and
`Researcher: ... S12 ... → ... S13 ...`. The "Current Focus" block
gets a new S13 section AND preserves the prior S12 cascade table
under a new "Prior STATE-SYNC: S12 (PR #19334)" heading for
historical continuity.

### meta.json (already at verified state from S12)

```
$ jq '.meta | {status, badge, lineCount, axiomCount, sorries, theoremCount, definitionCount, mathlib_version}' \
    src/data/proofs/ehrhart-cube-proven-oq-04/meta.json
{
  "status": "verified",
  "badge": "verified",
  "lineCount": 775,
  "axiomCount": 0,
  "sorries": 0,
  "theoremCount": 30,
  "definitionCount": 2,
  "mathlib_version": "4.26.0"
}
```

meta.json was correctly updated by S12. No S13 edits to meta.json.

### Research JSON (the drift to fix)

Pre-S13 the file was last touched at PR #18939 (S7 POLY-COROLLARIES,
2026-05-13) per `git log --oneline -- src/data/research/problems/ehrhart-cube-proven-oq-04.json`.
Post-S13 this PR is the most recent touch.

## 4. Build verification (re-confirmed from PR #19101 metadata, not re-run)

S13 STATE-SYNC is **doc-only** and does NOT re-run Docker build.
The build status is inherited from PR #19101 (S9 ACT mechanic fix,
commit `be08fef58bb`, merged 2026-05-15T22:59:15Z), which reported:

```
$ ./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ04
✔ [7743/7743] Built Proofs.EhrhartCubeProvenOQ04 (10s)
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

Mathlib pin at PR #19101 merge time: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
Mathlib pin at S13 write time (verified via `proofs/lake-manifest.json`):
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **Unchanged** — no
toolchain drift since PR #19101 merged. Build inheritance valid.

If at some future S## the Mathlib pin moves, the S15 regression-check
plan (state.md "Next Action" §S15) prescribes re-running the Docker
build before any new research lands. S13 STATE-SYNC does NOT trigger
that — the pin is unchanged, the file is unchanged, no rebuild
needed.

## 5. Conflict-free guarantees

This S13 STATE-SYNC PR touches exactly **three** files:

1. `src/data/research/problems/ehrhart-cube-proven-oq-04.json`
   (12 fields updated; 5 confirmed unchanged)
2. `research/problems/ehrhart-cube-proven-oq-04/state.md`
   (head re-rewritten to S13; prior S12 cascade table preserved
   under "Prior STATE-SYNC: S12 (PR #19334)"; "Next Action" §
   renumbered S13→S14, S14→S15, +S16, +S17; "Attempt Counts" §
   bumped 12→13 entries)
3. `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s13-state-sync-research-json-catchup.md`
   (new file, this note)

**Not touched** (intentional, conflict-free):
- `proofs/Proofs/EhrhartCubeProvenOQ04.lean` — Lean source
  unchanged, verified at PR #19101 / Mathlib pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- `src/data/proofs/ehrhart-cube-proven-oq-04/meta.json` — already
  current from S12 STATE-SYNC (`status: verified`, `badge: verified`,
  `lineCount: 775`, `theoremCount: 30`)
- Any sibling-slug files — single-slug PR
- Any S1-S12 session memos — preserved verbatim

**Open PR check** (`gh pr list --search "ehrhart-cube-proven-oq-04
in:title" --state open` at S13 write time): 0 matches. No open peers
to coordinate with.

## 6. Orthogonality manifest

S13 STATE-SYNC's edits do not block any of:
- S14 Mathlib upstream contribution (the JSON `nextSteps` lists
  S14 as the first forward item; once S14 starts, that next-step
  becomes the active focus)
- S15 prospective regression check (no edits required until a
  Mathlib pin bump triggers it)
- S16 Polynomial-degree corollary (new Lean theorem; S13 doc-only
  has no source-file footprint to merge-conflict with S16's Lean
  edit)
- S17 Hermit cross-gallery scan (out of this slug's scope; doc-only
  cross-references possible but not required)

Any of S14/S15/S16/S17 can start independently after S13 STATE-SYNC
merges. No claim-script changes required (slug stays `active`
through S14+; only flips to `completed` at slug-level termination,
which is a Champion/Deployer decision, not a Researcher one).

## 7. Why this is a STATE-SYNC, not a fresh phase

The MEMORY catalogue contains a feedback entry titled
"Researcher — post-ship pivot lands on slug where recent ACT did
partial inline STATE-SYNC leaving N drift items, ship full STATE-SYNC
closing them" (researcher-12 2026-05-16T04:38-04:50Z post-PR#19439
analog). This S13 STATE-SYNC fires the same pattern with one
adaptation: S12's predecessor wasn't a partial inline STATE-SYNC of
an ACT — it was an EXPLICIT scoped STATE-SYNC that deliberately
excluded the research-JSON file (per S12 §10 "Conflict-free
guarantees"). The drift is still 12 items, the resolution is still
doc-only, the iteration still bumps by exactly 1. No claim is
released mid-session; no `update-status` flips are needed.

**Iteration semantics**: each STATE-SYNC bumps the iteration counter
by 1. S12 STATE-SYNC was iteration 12 (state.md L5 pre-S13). S13
STATE-SYNC is iteration 13 (state.md L5 post-S13). Future STATE-SYNCs
will continue this convention.

## 8. Risk analysis

| Risk | Likelihood | Mitigation |
|---|---|---|
| JSON syntax error breaking `jq` consumers | LOW | `jq empty src/data/research/problems/ehrhart-cube-proven-oq-04.json` validates at edit time |
| `lastUpdate` timestamp inconsistency with `currentState.since` | LOW | `lastUpdate` reflects this PR's write moment; `since` reflects the S9 ACT merge moment. Different semantics, intentionally different values. |
| Drift between state.md "Iteration" head and JSON `currentState.iteration` | NONE | Both bumped 12→13 in this PR. |
| Future Mathlib bump silently invalidates the inherited build claim | DEFERRED to S15 | The S15 plan in state.md "Next Action" prescribes re-running Docker on any pin change. |
| Lean file count drift vs JSON `leanFiles[1].lineCount` | NONE | `wc -l` returned 775, JSON now records 775. |
| `theoremCount` drift if a future doc-only PR adds an `example` | LOW | `theoremCount` excludes `example`. `grep -c "^theorem\|^lemma..."` yields 30 currently. |
| meta.json drift (S12 set status/badge/lineCount, future S## might miss) | NONE | meta.json fields are tracked separately; S13 does not touch meta.json, so no drift introduced here. |

## 9. Handoff / Next-action picker recipe

Successor researcher claiming this slug after S13 merges should:

1. Read state.md head — confirm `Iteration: 13`, `Phase: VERIFIED`,
   `Since: 2026-05-15T22:59:15Z`.
2. Read state.md "Next Action" — choose between S14 (Mathlib
   upstream, ~6-stage PR), S15 (regression check, contingent on
   Mathlib pin change), S16 (polynomial-degree corollary, ~25-40
   LOC), S17 (Hermit cross-gallery scan, Hermit-scope).
3. Verify Mathlib pin via `cat proofs/lake-manifest.json | jq -r
   '.packages[] | select(.name=="mathlib") | .rev'`. If
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, S15 regression-check
   is NOT triggered. If different, run S15 first.
4. For S14 (Mathlib upstream): see
   `sessions/2026-05-15-s12-state-sync-build-verified.md` §7 for
   the contribution map.
5. For S16 (polynomial-degree): paste-ready sketch — `theorem
   cubeHStarPoly_natDegree (d : ℕ) (hd : 0 < d) : (cubeHStarPoly
   d).natDegree = d - 1 := by ...` using
   `Polynomial.natDegree_eq_of_coeff_ne_zero_of_le` with the leading
   coefficient `(cubeHStarPoly d).coeff (d - 1) = A(d, d-1) = A(d, 0)
   = 1` discharged via `cube_h_star_eulerian` + `eulerian_palindrome`
   + `eulerian_zero_eq_one`. Estimated 25-40 LOC, 1-2 Docker iters.

## 10. PR title

`research(ehrhart-cube-proven-oq-04): S13 STATE-SYNC — research-JSON catchup post-S12 verified-state confirmation (doc-only)`

## 11. Files touched

```
src/data/research/problems/ehrhart-cube-proven-oq-04.json    # 12 field updates
research/problems/ehrhart-cube-proven-oq-04/state.md         # iteration bump + S13 focus block + Next-Action renumber
research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-15-s13-state-sync-research-json-catchup.md  # NEW
```

No Lean source edits. No `meta.json` edits. No sibling-session edits.
No parent-file edits. No build re-run (inherited from PR #19101).
