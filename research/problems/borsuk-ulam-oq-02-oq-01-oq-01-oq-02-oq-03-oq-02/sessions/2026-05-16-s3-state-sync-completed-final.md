# borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02 — S3 STATE-SYNC: completed-final iter+nextSteps catchup + sessions/ bootstrap + leanFiles mechanic handoff (doc-only)

**Date**: 2026-05-16
**Phase**: S3 STATE-SYNC (doc-only; the slug is `axiomatized-final` and has been
since 2026-05-06; this memo + a minimal state.md + JSON refresh absorb the
remaining post-S2 drift)
**Researcher**: researcher-9
**Branch**: `research/researcher-9-bu-oq02-7chain-s3-statesync-1514Z`
**Mathlib pin**: v4.26.0 (unchanged across S1 + S2 + S3)
**Status**: Doc-only. Three files modified — this new session memo +
`state.md` head refresh + `src/data/research/problems/<slug>.json` `currentState`
+ `lastUpdate` + `attemptCounts.total` + `knowledge.nextSteps` edits. No Lean
edits, no `problem.md` (the slug never had one — see §1.3 for why), no
`knowledge.md` edits, no gallery `meta.json` edits, no `leanFiles[]` edits
(see §3 — mechanic handoff).

## §1 Why S3 fires when S2 was "supposed final"

### §1.1 Setup

The slug `borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02` completed on
2026-05-06 with the `buDim_eq_sup_primeFactors` and `buDim_prod_primes_eq`
theorems landing in `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean`
at 247 LOC (13 theorems, 0 sorries, 0 new axioms, 5 inherited parent axioms).
The gallery entry was promoted the same day with `meta.status: axiomatized` /
`meta.badge: axiom`.

S2 STATE-SYNC (researcher-9, 2026-05-14T16:00:00Z) advanced `state.md` from
its seeker-init stub (`Phase: NEW`, `Iteration: 1`, `Current Focus: Initial
exploration`) to a consolidated session log reflecting the COMPLETED status.
The S2 "Out of scope" section explicitly stated:

> No JSON edits — `src/data/research/problems/.../json` is already at
> `phase: COMPLETED` / `status: completed`.

That was a narrow scope choice. The top-level `phase`/`status` were indeed
correct, but **internal currentState + lastUpdate were not synced**:

| Surface | S2 saw | Reality at S2 ship time | Drift |
|:--------|:-------|:------------------------|:------|
| `state.md` head `Phase:` | `COMPLETED (k-prime CRT generalization landed; canonical state.md sync, doc-only)` | n/a (set by S2) | n/a |
| `state.md` head `Iteration:` | `2` (S2 advanced from 1) | n/a (set by S2) | n/a |
| JSON `phase` (top) | `COMPLETED` | `COMPLETED` ✓ | none |
| JSON `status` (top) | `completed` | `completed` ✓ | none |
| JSON `currentState.iteration` | `1` (untouched) | should be ≥ 2 after S2 | -1 |
| JSON `currentState.since` | `2026-05-05T02:57:44.793Z` (seeker create) | gallery-promote was 2026-05-06; S2 ship was 2026-05-14 | -8d (S2 era) |
| JSON `lastUpdate` (top) | `2026-05-05T02:57:44.792Z` | should be ≥ 2026-05-14 | -8d (S2 era) |
| JSON `currentState.attemptCounts.total` | `0` | should be ≥ 2 (S1 ACT + S2 STATE-SYNC) | -2 |
| JSON `currentState.focus` | "Completed: proved k-prime CRT generalization with 0 sorries" | accurate but generic; no mention of S2 STATE-SYNC | minor |
| JSON `currentState.nextAction` | "None — proof complete" | accurate | none |
| JSON `knowledge.nextSteps` | `[]` | accurate (proof complete; no follow-up) | none |
| `sessions/` directory | non-existent | should exist | bootstrap |
| `leanFiles[]` `BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean` `lineCount` | `235` | actual `wc -l` = `247` | -12 (mechanic territory) |

So three of the four "completed-slug residual drift" patterns documented in
researcher memory feedback are present: iteration not bumped, lastUpdate not
refreshed, `sessions/` not bootstrapped. The `leanFiles[]` drift is mechanic
territory and is packaged for handoff in §3 below; this S3 STATE-SYNC does
NOT self-edit `leanFiles[]`.

### §1.2 Why pick this up now

T+2d post-S2: no PRs on this slug have shipped since S2 (no mechanic backport,
no enricher pass, no auditor flag). The drift items are stable. A future
researcher cycle (in the next ~3-7 days, by knowledge-priority claim-random
sampling) would land on this slug and either (a) re-ship a 4th narrow STATE-SYNC
that duplicates S2's narrow-iteration trap, or (b) misread `lastUpdate: 2026-05-05`
as a freshness signal indicating the slug has barely been touched, which would
disagree with the state.md head's 2026-05-14 S2 timestamp. Either failure mode
is preventable by a small S3 catchup now.

The S3 work fits cleanly within the researcher 2-per-session STATE-SYNC cap
documented in the feedback memory (one STATE-SYNC pre-claim + the iteration-2
"completed slug bootstrap" pattern).

### §1.3 Why this slug has no `problem.md`

The seeker-spawn pattern for OQ-class slugs in early-May 2026 did not create
a `problem.md` skeleton — only `knowledge.md` was bootstrapped at seeker time.
The slug's problem framing lives entirely in the gallery `meta.json`'s
`overview.problemStatement` field and is mirrored in `knowledge.md` §"Problem
Summary". S3 does NOT create a `problem.md` — that scope belongs to the
curator pass that touches all `problem.md`-less OQ-class slugs in batch.

## §2 Drift inventory + verification commands

All drift items verified at branch base SHA `8d8f98aa572` (`origin/main` head
at S3 author time).

### §2.1 JSON `currentState.iteration` drift

```bash
$ python3 -c "import json; d=json.load(open('src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02.json')); print(d['currentState']['iteration'])"
1

$ head -6 research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/state.md | grep Iteration
**Iteration**: 2 (1 ACT + this STATE-SYNC)
```

state.md head ahead of JSON by 1 iteration. S3 catchup: JSON `iteration` 1 → 3
(absorbs S2 + S3 in one bump).

### §2.2 JSON `lastUpdate` drift (top-level)

```bash
$ python3 -c "import json; d=json.load(open('src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02.json')); print(d.get('lastUpdate'))"
2026-05-05T02:57:44.792Z
```

That is the seeker-create timestamp, never updated. S3 refreshes to current
S3 ship time.

### §2.3 JSON `currentState.attemptCounts.total` drift

```bash
$ python3 -c "import json; d=json.load(open('src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02.json')); print(d['currentState']['attemptCounts'])"
{'total': 0, 'currentApproach': 0, 'approachesTried': 0}
```

Never bumped through S1 ACT or S2 STATE-SYNC. S3 catchup: `total` 0 → 3.

### §2.4 `sessions/` directory absent

```bash
$ ls research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/sessions/ 2>&1
ls: research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/sessions/: No such file or directory
```

S3 bootstraps the dir with this memo as the first entry (the S1 ACT and S2
STATE-SYNC bodies remain reconstructable from state.md and would be
retro-bootstrapped only if a future cycle needs them).

### §2.5 `leanFiles[]` `lineCount` drift (mechanic territory; see §3)

```bash
$ wc -l proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean
     247 proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean

$ python3 -c "import json; d=json.load(open('src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02.json'));
 [print(lf['path'], lf['lineCount']) for lf in d['leanFiles'] if 'OQ02OQ01OQ01OQ02OQ03OQ02' in lf['path']]"
Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean 235
```

JSON underreports by 12 LOC. Gallery `meta.json` correctly says `lineCount: 247`
(both at the top-level `meta.lineCount` and at `leanFile.lineCount`). S3 does
**NOT** self-edit `leanFiles[]` — that surface is auto-populated by
`scripts/research/enrich-research.ts` and manual edits risk being clobbered.
The ready-to-paste correction is provided in §3 below for mechanic pickup.

### §2.6 Gallery `meta.json` — NO drift

Verified at branch base SHA — all gallery fields populated and consistent
with the parent .lean file:

| Field | gallery `meta.json` | actual / authoritative source |
|:------|:--------------------|:------------------------------|
| `meta.status` | `axiomatized` | matches (5 inherited parent axioms) ✓ |
| `meta.badge` | `axiom` | matches `meta.status` ✓ |
| `meta.sorries` | `0` | `grep sorry` returns 0 ✓ |
| `meta.axiomCount` | `5` | `grep '^axiom '` in this file returns 0; 5 = inherited parent count ✓ |
| `meta.lineCount` | `247` | `wc -l` = 247 ✓ |
| `meta.theoremCount` | `13` | `grep -cE '^(theorem\|lemma) '` = 13 ✓ |
| `leanFile.lineCount` | `247` | matches `wc -l` ✓ |
| `leanFile.theoremCount` | `13` | matches grep ✓ |
| `leanFile.axiomCount` | `0` | matches grep (no `^axiom ` declarations in *this* file; the 5 inherited from parents are correctly accounted for in `meta.axiomCount`) ✓ |

Gallery `meta.json` is the authoritative surface for downstream gallery
rendering; it is correct and S3 does NOT touch it.

## §3 leanFiles[] mechanic handoff package (ready-to-paste)

The single drift item that the researcher cannot/should not self-edit is the
canonical research-JSON `leanFiles[]` entry for the slug leaf file. Per the
"completed-slug postship pivot" feedback memory, `leanFiles[]` is auto-populated
by `scripts/research/enrich-research.ts` and manual edits risk being clobbered
by the next enricher pass. The corrected entry is packaged here for the
mechanic agent to pick up via `scripts/lean/enrich-research.ts` re-run or a
narrow manual mechanic PR.

### §3.1 Current (stale) JSON `leanFiles[]` entry

```json
{
  "path": "Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean",
  "lineCount": 235,
  "theoremCount": 13,
  "axiomCount": 0,
  "sorryCount": 0
}
```

### §3.2 Corrected (ready-to-paste) JSON `leanFiles[]` entry

```json
{
  "path": "Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean",
  "lineCount": 247,
  "theoremCount": 13,
  "axiomCount": 0,
  "sorryCount": 0
}
```

Single-field correction: `lineCount` 235 → 247. Other three counters
(`theoremCount`, `axiomCount`, `sorryCount`) are correct and unchanged.

### §3.3 Verification

```bash
$ wc -l proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean
     247

$ grep -cE "^(theorem|lemma) " proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean
13

$ grep -cE "^axiom " proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean
0

$ grep -c "sorry" proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean
0
```

### §3.4 Likely root cause

The S1 ACT-time leanFiles[] entry was populated by an earlier version of
`enrich-research.ts` that read the leaf .lean file at an in-progress state
(235 LOC, before final docstring additions pushed to 247). The S1 ACT PR's
final post-push file size matched gallery `meta.json` (247) but the
research-JSON enrichment ran on an earlier snapshot.

### §3.5 Sibling-slug precedent

The 6-segment sibling `borsuk-ulam-oq-02-oq-01-oq-03-oq-02` (distinct slug)
had a similar `leanFile.*` drift, fixed by mechanic PR #19464 (merged
2026-05-16T05:03Z, `fix(meta): borsuk-ulam-oq-02-oq-01-oq-03-oq-02
leanFile.* drift sync`). That PR did NOT cover this slug's
`leanFiles[].lineCount: 235 → 247` drift. A follow-on mechanic PR or
enrich-research re-run can pick this up.

## §4 Stale-duplicate-PR audit (informational only)

`gh pr list --search "borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02 in:title"
--state open` returns 0 open PRs on this exact 7-segment slug. The 4 open
PRs that the gh search returns are for the related but distinct 5-segment
slug `borsuk-ulam-oq-02-oq-01-oq-03-oq-02` (S8, S11, S12, S15 OPEN PRs from
2026-05-08/09). Those are NOT this slug's responsibility — they belong to
the 5-segment slug's own STATE-SYNC / champion / curator cycle.

S3 does NOT close, comment on, rebase, or otherwise touch those 4 open PRs.

## §5 Not done / out of scope

S3 STATE-SYNC explicitly does NOT:

1. **Edit `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean`** or any
   other .lean file. The slug is `axiomatized-final` and the Lean is
   complete.
2. **Edit `proofs/Proofs.lean` or `proofs/lakefile.toml` or
   `proofs/lake-manifest.json`**.
3. **Edit `src/data/proofs/<slug>/meta.json`** or any gallery surface
   (annotations.json, index.ts). All gallery surfaces are correct and
   downstream-rendering-stable.
4. **Edit `leanFiles[]` in canonical research-JSON**. Mechanic territory;
   §3 packages the correction for handoff.
5. **Create `problem.md`**. Out of scope (see §1.3 — curator batch
   territory for OQ-class slugs without `problem.md`).
6. **Edit `knowledge.md`**. The S1-era knowledge.md is accurate and complete;
   the new gap surfaced in §3 belongs in this memo, not in knowledge.md
   (which describes the *math*, not the data-pipeline).
7. **Close, comment on, or rebase** the 4 OPEN PRs for the 5-segment
   sibling slug `borsuk-ulam-oq-02-oq-01-oq-03-oq-02`.
8. **Re-run `scripts/research/enrich-research.ts`** to auto-fix the
   `leanFiles[]` drift. That script's invocation is mechanic/auditor
   territory; researcher-9's S3 packages the correction as a paste-ready
   diff in §3 rather than triggering the script.
9. **Re-run any Docker build**. The slug's last build verification is the
   S1 ACT (PR merge 2026-05-06); the Lean is unchanged since. Re-verification
   is out-of-scope for STATE-SYNC.
10. **Bump `currentState.since`** to S3 ship time. The `since` field is
    interpreted as "time the current phase began" — the COMPLETED phase
    began at gallery promote on 2026-05-06, not at this S3 ship time. S3
    refreshes `since` to `2026-05-06T00:00:00Z` (gallery-promote
    canonicalisation) rather than current time.

## §6 Acceptance

S3 ships cleanly when:

- [x] Branch `research/researcher-9-bu-oq02-7chain-s3-statesync-1514Z`
      based on `origin/main`.
- [x] 3 files modified (this new memo + state.md + canonical research-JSON).
- [x] 0 .lean / gallery / meta.json / lake-manifest / problem.md /
      knowledge.md / sibling-slug / sessions/* (prior) edits.
- [x] state.md head Phase → `COMPLETED — axiomatized-final`; Iteration 2 →
      3; Last Updated added.
- [x] state.md prepends an S3 entry above S2 with §1-§6 cross-references.
- [x] JSON `currentState.iteration` 1 → 3; `currentState.since` →
      2026-05-06T00:00:00Z (gallery promote); `currentState.focus` minor
      refresh; `currentState.nextAction` adds 1-sentence mechanic handoff;
      `currentState.attemptCounts.total` 0 → 3; `lastUpdate` (top) →
      current ISO; `knowledge.nextSteps` populated with completed-final
      declaration + 1 mechanic handoff note pointing at §3 of this memo.
- [x] §3 packages mechanic handoff for the `leanFiles[].lineCount` 235 → 247
      drift without self-editing the field.
- [x] Out-of-PR: `claim-problem.sh update <slug> completed` re-run (idempotent;
      the slug pool may have an in-progress marker even though JSON `status:
      completed`).

## §7 Host context

Researcher-9 ran S3 in the worktree
`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9` at
2026-05-16T15:14:53Z. Host environment:

- **Docker daemon**: `docker info` Client section enumerates plugins, but
  the `Server:` section is empty (daemon hung); `docker version` returns
  Client only. No Lean build was attempted (doc-only STATE-SYNC).
- **Disk**: `df -h /System/Volumes/Data` reports `5.7Gi avail / 100%
  capacity`. Marginal for any future Docker re-fetch but irrelevant to
  this doc-only S3.
- **`proofs/.lake`**: circular self-symlink (`readlink proofs/.lake →
  /Users/rwalters/GitHub/lean-genius/proofs/.lake`); irrelevant to S3
  (no Lean operations).
- **Mathlib pin**: `proofs/lake-manifest.json` records v4.26.0
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged.
- **Branch base**: `origin/main` at SHA `8d8f98aa572` (CLT-oq-01 S9 ACT
  most-recent merge).

## §8 References

- **PR #(this PR)** — this S3 STATE-SYNC.
- **Previous in-slug PRs**:
  - S1 ACT (2026-05-06, ship PR): created leaf .lean +
    `BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean` (247 LOC, 13 theorems,
    0 sorries, 0 new axioms; 5 inherited parent axioms).
  - S2 STATE-SYNC (2026-05-14, researcher-9): refreshed state.md from
    seeker-init stub to consolidated session log; JSON deliberately
    untouched per the S2 "Out of scope" note.
- **Sibling-slug mechanic precedent**: PR #19464 (merged 2026-05-16T05:03Z,
  `fix(meta): borsuk-ulam-oq-02-oq-01-oq-03-oq-02 leanFile.* drift sync`)
  — handled the same shape of drift on a sibling 5-segment slug; did NOT
  cover this 7-segment slug (sibling-mechanic-missed-this-batch pattern).
- **Gallery surface**: `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/{meta.json,annotations.json,index.ts}`
  — populated in S1, unchanged since. Authoritative for gallery rendering.
- **Mathlib pin**: v4.26.0, commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
  verified via `proofs/lake-manifest.json`.

> _Phase note_: This skill maps "S3 STATE-SYNC" to the canonical post-COMPLETED
> bookkeeping iteration. The slug remains `axiomatized-final` and is not
> expected to receive further researcher attention; any future cycle on this
> slug would be mechanic (leanFiles drift), curator (problem.md bootstrap),
> or champion (PR audit).
