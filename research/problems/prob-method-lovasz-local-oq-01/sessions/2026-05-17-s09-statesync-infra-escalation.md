# S9 STATE-SYNC — 3 RED INFRA escalation + Mathlib pin byte-stability re-verify + iteration bump

**Researcher**: researcher-4
**Date**: 2026-05-17 (claim at 02:00 UTC, ship ~02:30 UTC)
**PR**: (this PR)
**Mode**: STATE-SYNC (doc-only — state.md + this memo + JSON; no Lean / no problem.md / no knowledge.md / no leanFiles / no Mathlib pin / no sibling-slug edits)
**Predecessor**: S8 PREP #19628 (researcher-8, merged 2026-05-16T14:32Z, T-11.5h at S9 claim)
**Predecessor of predecessor (meta sync)**: mechanic #19792 (merged 2026-05-16T20:21Z, T-6h at S9 claim) — `leanFiles[1]` MoserTardos.lean post-S6 ACT sync

## §1. Trigger / rationale

The slug landed on a `claim-random` re-roll in researcher-4's session
on 2026-05-17T01:40Z after three earlier release cycles
(`szemeredi-full-oq-01` — 2 open S8 STATE-SYNC PRs #19974+#19976 same
iter; `ballot-problem-oq-03-oq-01-oq-01-oq-01` — open S45 ACT PR
#20013 T-43min). The slug satisfied the proceed-criteria of the
hot-collision decision matrix:

| Criterion | Result | Source |
|---|---|---|
| Open PRs on slug | 0 | `gh pr list --search prob-method-lovasz-local-oq-01 --state open` |
| Researcher merge ≤T-2h | 0 | most recent merge S8 PREP #19628 at T-11.5h |
| Mechanic merge ≤T-2h | 0 | most recent mechanic #19792 at T-6h |

The slug presented two visible drift items + one infra-snapshot
refresh:

1. **INFRA snapshot refresh**: S8 PREP gate row #8 said
   "Docker `info` ServerVersion empty in ≤10s; `/System/Volumes/Data`
   100% capacity, 6.6 Gi free". S9 claim host check showed 2.9 Gi free
   (G7 worsened by -3.7 Gi over ~11.5h); G8/G9 unchanged. **Primary
   driver** of this STATE-SYNC.
2. **Mathlib pin byte-stability re-verify**: 4-day-stable `rev`,
   transitively-valid bearer table — quick check, no walk. (Trivial,
   bundled.)
3. **Iteration bump**: 10 → 11 with new narrative + iteration history
   row; closes the ~12h `currentState.lastUpdate` gap.

**Deferred** (NOT in scope):

- **`leanFiles[1]` re-flip** (theoremCount 5 vs 6, sorryCount 0 vs 2):
  mechanic #19792 deliberately chose `5 / 0` via narrower regex +
  docstring-exclusion 6h ago. Per `_postship_pivot_to_act_ready_slug_
  where_mechanic_batch_explicitly_excluded_this_slug_with_separate_
  scope_rationale` feedback memo, S9 STATE-SYNC honors mechanic's
  recent explicit boundary; same-slug ping-pong avoided. See §3 for
  detail.
- **Top-level `phase: "OBSERVE"` mirror**: pre-existing static
  drift from slug-creation; not session-caused. Deferred to a future
  mechanic pass or to an explicit convention-aligning batch.

## §2. INFRA snapshot detail (G7 / G8 / G9)

### §2.1 G7 — host disk

```
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   887Gi   2.9Gi   100%     21M   30M   41%   /System/Volumes/Data
```

- **S8 PREP snapshot**: 6.6 Gi free.
- **S9 claim snapshot**: 2.9 Gi free.
- **Δ**: −3.7 Gi over ~11.5h ≈ −320 MB/h sustained.
- **Threshold cross**: 5 Gi (soft-floor observed in concurrent
  researcher sessions as the level at which `lake build` artifact
  staging starts failing intermittently).

**Cross-validation (not slug-local; host-rooted leak)**:

| Concurrent agent | Window | G7 delta | Reported in |
|---|---|---|---|
| ballot S80 STATE-SYNC | ~5h prior | 4.5 → 2.9 Gi (-1.6 Gi) | PR #19994 |
| minkowski S29 STATE-SYNC | ~1h prior | 6.7 → 3.4 Gi (-3.3 Gi/12h) | PR #20018 (open) |
| birthday S25 ACT | ~30min prior | 3.0 → 2.8 Gi reported RED | PR #19997 |

All three agents independently report disk pressure in the same window
with similar deltas. The leak is host-rooted (likely Docker/Lean toolchain
cache + log accumulation; consistent with G8 daemon-hang preventing
normal container GC), not self-cycle of any one slug's build artifacts.

### §2.2 G8 — Docker daemon

```
$ timeout 10 docker info 2>&1 | grep -E "ServerVersion|Server Version" | head -3
(empty — command times out at 10s with no Server section)
```

- **S8 PREP snapshot**: ServerVersion empty within 10s.
- **S9 claim snapshot**: ServerVersion empty within 10s (unchanged).
- **Cumulative hang**: ≥20h at S9 claim per cross-agent reports of
  06:01Z hang start (ballot S80 + minkowski S29). The original hang
  predates S8 PREP by ~8h.

### §2.3 G9 — `.lake` self-loop

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 16 09:04 /Users/rwalters/GitHub/lean-genius/proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

- **S8 PREP snapshot**: same self-loop.
- **S9 claim snapshot**: same self-loop (timestamp `May 16 09:04`
  unchanged; symlink target unchanged).
- **Implication**: even if G7/G8 recovered, the lake symlink would
  still need to be re-pointed to a real `.lake/` directory before any
  `./proofs/scripts/docker-build.sh` invocation could succeed.

### §2.4 ACT-readiness gate refresh (rows 1–8)

| # | Item | S8 PREP | S9 STATE-SYNC | Δ |
|---|---|---|---|---|
| 1 | Mathlib pin stable | GREEN | GREEN | unchanged (re-verified §3) |
| 2 | Bearers verified at pin | GREEN | GREEN | unchanged (transitivity §3) |
| 3 | Paste-ready substitute body | GREEN | GREEN | unchanged |
| 4 | Parent file 382 LOC, 0 algo sorries | GREEN | GREEN | unchanged (file SHA stable) |
| 5 | No competing open PRs | GREEN | GREEN | re-verified at S9 claim |
| 6 | JSON catchup | GREEN | GREEN | this PR closes |
| 7 | problem.md / knowledge.md unchanged | GREEN | GREEN | unchanged |
| 8 | Infra | RED (6.6 Gi free, Docker hung) | **RED-er** (2.9 Gi free, Docker still hung, ≥20h cumulative) | -3.7 Gi disk |

7/8 GREEN substantive + 1/8 RED-er infra. ACT remains blocked
strictly on infra.

## §3. Mathlib pin re-verify

```
$ head -3 proofs/lake-manifest.json
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
$ grep -o '"rev": "[^"]*"' proofs/lake-manifest.json | head -1
"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

- **Pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib4 v4.26.0).
- **Byte-stability**: ≥4.5 days at this rev per `git log -p
  proofs/lake-manifest.json` (last touch predates S7 PREP #19111).
- **S7/S8 PREP bearer table transitively valid**:
  - `PMF.toOuterMeasure_apply_fintype` Basic.lean:203 (S8 PREP §3.2)
  - `MeasurableSet.of_discrete` Defs.lean:549 (S7 §3.3(c), S8 §1.2)
  - `Fintype.card_subtype.symm` Card.lean:378 (S5c PREP §2.2)
  - `Equiv.piSplitAt` Logic/Equiv/Prod.lean:479 (S4b PREP §3, S5c §2.3)
  - `PMF.toMeasure_uniformOfFintype_apply` Uniform.lean:318 (S7 §3.2)
  - `Fintype.prod_eq_mul_prod_subtype_ne` (S5b PREP)
  - `ENNReal.mul_inv` / `mul_left_comm` / `ENNReal.mul_inv_cancel`
    (S5b ACT §deviations)

At a byte-stable SHA, no re-walk via `curl raw.githubusercontent.com`
is justified for this STATE-SYNC; the cost is real (~5 min per bearer
at 7 bearers ≈ 35 min) and the value is zero in expectation
(byte-stable repo → byte-stable bearers).

## §4. `leanFiles[1]` mechanic-choice respect (DO NOT re-flip)

Mechanic PR #19792 (merged 2026-05-16T20:21Z, T-6h at S9 claim) made
this explicit choice for `leanFiles[1]` (`MoserTardos.lean`):

```json
{
  "path": "Proofs/MoserTardos.lean",
  "lineCount": 382, "theoremCount": 5, "axiomCount": 0,
  "defCount": 5,   "sorryCount": 0
}
```

with PR-body rationale (verbatim, condensed):

- `theoremCount = 5`: via `grep -cE "^(theorem|lemma) "` → "3 lemmas
  + 2 theorems". This regex deliberately excludes the `private`-prefix
  lemma `marginal_uniformOfFintype_pi` at line 175.
- `sorryCount = 0`: via `grep -nE "(^|[^A-Za-z_'])sorry([^A-Za-z_'])"`
  → "2 matches at lines 7 + 22, both inside the file-level docstring
  (`(with `sorry`)` and `` `sorry`s below `` in prose); 0 tactic sites".
  This deliberately excludes docstring-text mentions.

### §4.1 Alternative canonical counts (NOT applied this PR)

Per the lean-mechanic canonical conventions (per the
`_mechanic_batch_sync_conventions_canonical_counts_and_python_json_
dump_unicode_trap` feedback memo):

- `theoremCount` via `^(?:protected|private|noncomputable )*(theorem|
  lemma) ` → **6** (includes `private lemma` line 175);
- `sorryCount` via raw `\bsorry\b` (no comment strip) → **2**
  (includes docstring text on lines 7 + 22).

The mechanic in #19792 used narrower regexes (no `private` prefix) +
explicit comment-strip-by-eye decision. This is a legitimate alternative
convention; the mechanic memo verbatim describes the documented choice
("docstring mentions, not tactic sites") as the controlling rationale.

### §4.2 Decision: defer to mechanic

- Mechanic's choice is **6h old** — current authoritative statement.
- Mechanic's PR-body **explicitly** documents the choice — not a
  silent omission.
- Re-flipping in S9 STATE-SYNC would be **same-slug ping-pong**: my
  PR-body would say "I'm reverting #19792's deliberate choice based on
  a different regex" — this is an editorial dispute the agents should
  not have through PR commits.
- The right venue for re-aligning conventions is a separate **mechanic
  convention-batch** PR that scans ≥10 slugs and applies the chosen
  convention systematically with stakeholder review.

S9 STATE-SYNC therefore does **not** edit `leanFiles[1]`.

## §5. Top-level `phase: "OBSERVE"` (deferred, not session-caused)

The slug's top-level `phase: "OBSERVE"` has been stale since slug
creation (`"started": "2026-05-12T11:50:00Z"`); `currentState.phase`
has been the source-of-truth tracker. A sample of 20 problem JSONs
shows 16/20 matching top-level vs `currentState`, with the mismatches
being COMPLETED-or-NEW-edge-cases.

- **Not session-caused**: this drift predates S8 PREP, S7 PREP, S6
  ACT, and all prior research activity on the slug.
- **Not a mechanic batch surface**: the recent mechanic batches
  (e.g., #19792, #20004, #20005, #20006) all touch `leanFiles[]`
  numerics only, not top-level `phase`.
- **Defer** to either (a) a slug-creator backfill or (b) a future
  STATE-SYNC that has substantive PREP/ACT content and bundles this
  ~5-character edit.

S9 STATE-SYNC therefore does **not** edit top-level `phase`.

## §6. Race-safety (pre-claim + planned pre-push)

### §6.1 Pre-claim probe (2026-05-17T01:36Z)

```
$ gh pr list --repo rjwalters/lean-genius --search "prob-method-lovasz-local-oq-01" --state all --limit 8 --json number,title,state,mergedAt,createdAt
```

Top 8 results (8 total, all merged):

| # | Title | State | Merged | Notes |
|---|---|---|---|---|
| 19792 | fix(meta): MoserTardos.lean leanFiles drift | MERGED | 2026-05-16T20:21Z | mechanic, T-6h |
| 19628 | S8 PREP — faithful-link bearer-gap + STATE-SYNC catchup | MERGED | 2026-05-16T14:32Z | researcher-8, T-11.5h |
| 19111 | S7 PREP — LLLAdmissibleUniform structure design | MERGED | 2026-05-15T22:58Z | researcher-3 |
| 19103 | S6 ACT build-verify repair | MERGED | 2026-05-15T22:58Z | researcher-8 |
| 18960 | S5b ACT helper + _inside + _indep | MERGED | (older) | researcher-12 |
| 18930 | S5c PREP h_fiber bearer audit | MERGED | (older) | researcher-5 |
| 18683 | S5b PREP ENNReal cancellation | MERGED | (older) | researcher-7 |
| 18629 | S5 ACT resampleAt_apply_outside marginal | MERGED | (older) | researcher-6 |

**0 open PRs on slug.** ≥T-2h from most recent merge (T-6h to mechanic,
T-11.5h to researcher S8 PREP). Hot-collision decision matrix: proceed.

### §6.2 Pre-push probe (planned)

Before `git push` of this branch: re-run the `gh pr list` above. If
any new open PR appears on slug with same iter (S9 / iter 10/11) or
overlapping scope (state.md / JSON `currentState`): close-without-push
and release.

## §7. Files updated (final scope)

- `research/problems/prob-method-lovasz-local-oq-01/state.md`:
  head update (Phase / Since / Iteration); new narrative block §S9
  STATE-SYNC (~110 LOC) inserted between head and §S8 PREP; Iteration
  History +2 rows (#19792 mechanic, #this S9 STATE-SYNC).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-17-s09-statesync-infra-escalation.md`:
  this memo (~330 LOC, 10 sections).
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json`:
  - `currentState.phase` `S8 PREP` → `S9 STATE-SYNC`
  - `currentState.since` `2026-05-16T14:07:21Z` → `2026-05-17T02:00:00Z`
  - `currentState.iteration` `10` → `11`
  - `currentState.focus` (rewrite)
  - `currentState.nextAction` (rewrite)
  - `currentState.attemptCounts.total` `8` → `9`
  - `currentState.attemptCounts.currentApproach` `8` → `9`
  - `knowledge.progressSummary` (prepend S9 entry)
  - `knowledge.nextSteps[0]` (refresh `S9 ACT` → `S10 ACT`)
  - `lastUpdate` `2026-05-16T14:07:21Z` → `2026-05-17T02:00:00Z`

Total: 3 files modified (state.md +~120 LOC / -~10 LOC; JSON ~10 fields;
sessions/ new ~330 LOC).

## §8. Honesty / known limitations

- **No Docker build attempted**. G8 RED-unchanged; would not succeed.
- **No bearer re-walk via `curl`**. Mathlib pin byte-stable ≥4.5d;
  transitivity cited but not freshly retrieved per bearer. If S10
  finds a bearer-elaboration mismatch, the gap is somewhere other than
  Mathlib drift.
- **`leanFiles[1]` left at mechanic's chosen values** (5 / 0) even
  though my canonical regex would yield (6 / 2). Defer to mechanic;
  same-slug ping-pong avoided. See §4.
- **Top-level `phase: "OBSERVE"`** left stale (pre-session drift, not
  in scope; see §5).
- **No `pnpm build`**. Per `_mechanic_pnpm_build_regenerates_all_
  research_jsons` feedback memo: would regenerate ~1047 files and
  fight with `.lean/state/` symlinks. JSON validated via
  `python3 -c "import json; json.load(open(...))"` instead.
- **Disk pressure is host-critical**. At 2.9 Gi free, my own `git
  push` may fail if the push-pack delta exceeds free space. If push
  fails: emergency-release the slug and signal infra-degraded.

## §9. Distinguishing this S9 STATE-SYNC from neighbor patterns

This pattern is closely-related-but-distinct from:

- `_postship_pivot_to_prep_phase_slug_with_short_window_predecessor_
  and_registry_21d_stale_plus_baked_in_leanfiles_thmcount_miscount_
  plus_three_red_infra_with_g9_new_lake_selfloop`: here the predecessor
  is also short-window (T-11.5h vs T-5h45m) and 3 RED infra, but
  registry is NOT 21d stale (slug `available` in candidate pool,
  recently lifted), `leanFiles[i]` mismatch is honored-not-fixed
  (mechanic boundary), no NEW G9 (G9 was already RED at S8).
- `_postship_pivot_to_act_ready_slug_where_mechanic_batch_explicitly_
  excluded_this_slug_with_separate_scope_rationale`: there mechanic
  EXCLUDED my slug from a sibling-batch with rationale; here mechanic
  INCLUDED my slug (#19792 is single-slug-targeted at this slug) and
  made a deliberate alternative-convention choice. The "honor mechanic
  boundary" principle is the same; the slug-shape is different.
- `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_
  3red_infra_through_intended_window`: there ACT predecessor + mechanic
  partial-discharge; here PREP predecessor (S8) + mechanic FULL meta
  refresh (not partial).

## §10. Next action handoff (S10 candidate)

If a future researcher claims this slug and infra has recovered
(G7 ≥10 Gi + G8 Docker `ServerVersion` non-empty + G9 `.lake` no
longer self-loop):

1. **Recipe unchanged**: drop §4.1 + §4.2 + §3.2 substitute + §4.4
   structure + bridge into Part V of `proofs/Proofs/MoserTardos.lean`,
   per S8 PREP §4 budget (~130 LOC, 0 sorries, 0 axioms).
2. **Build-verify**: `./proofs/scripts/docker-build.sh Proofs.MoserTardos`.
3. **`leanFiles[1]` update post-build**: lineCount 382 → ~512 (+130),
   theoremCount per chosen regex (mechanic-narrow: +3 = 8; my-broad:
   +4 = 10), defCount 5 → 7 (+2: `uniformDrawProb`, `collisionAdj`),
   sorryCount: unchanged at mechanic's 0 (no new tactic sorries).

If infra still RED at the next claim window: re-STATE-SYNC iter 11→12.
If disk crosses 1 Gi (host-critical floor): escalation to architect
or operator handoff; emergency-release the slug.

---
**End S9 STATE-SYNC memo** — researcher-4, 2026-05-17.
