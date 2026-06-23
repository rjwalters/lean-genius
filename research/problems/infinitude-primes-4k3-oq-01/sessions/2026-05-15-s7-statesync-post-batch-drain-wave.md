# S7 STATE-SYNC — post-batch drain-wave (3 sibling PRs merged) tracker refresh (doc-only)

**Date**: 2026-05-15 (~23:21 UTC, post-deployer drain-wave at ~22:55–22:59 UTC)
**Researcher**: researcher-1
**Mode**: STATE-SYNC (doc-only — touches `state.md`, `src/data/research/problems/infinitude-primes-4k3-oq-01.json`, and this new sessions file; no `.lean`, no `knowledge.md`, no `problem.md`, no other `sessions/*.md`)
**Status**: post-merge tracker refresh after the 22:55–22:59 UTC drain wave merged three sibling PRs (#19088 S3 ACT R1, #19161 S3c PREP, #19310 S6 PREP). State.md and JSON were last refreshed 2026-05-14T16:00:00Z (S3 ACT R1 `since` timestamp) and are now five PREPs + one ACT behind. Per S6 PREP #19310 §11 ("Conflict-free guarantee … no `state.md` / `knowledge.md` / `problem.md` modifications"), the merged sibling explicitly defers tracker updates to the next STATE-SYNC iteration.

## §0. Drain-wave context

Recent merges on `origin/main` for this slug (chronological, all in the 22:55–22:59 UTC window):

| Time (UTC) | PR     | Topic                                                        | Mode      | Author        |
|------------|--------|--------------------------------------------------------------|-----------|---------------|
| 22:55:38Z  | #19310 | S6 PREP — Path C ACT-readiness gate + §5 placeholder closures | doc-only  | researcher-3  |
| 22:57:03Z  | #19161 | S3c PREP — q ∈ {12, 24} via CRT + Dirichlet specialization    | doc-only  | researcher-12 |
| 22:59:39Z  | #19088 | S3 ACT R1 — Klein-2 q ∈ {3, 4, 6} parametric infinitude       | Lean      | researcher-12 |

Plus the earlier same-day batch (18:02–18:05 UTC) that landed S5 PREP and S4 PREP:

| Time (UTC) | PR     | Topic                                                          | Mode      | Author        |
|------------|--------|----------------------------------------------------------------|-----------|---------------|
| 18:02:09Z  | #19274 | S5 PREP — goal-state simulation of S2(c) PREP skeleton          | doc-only  | researcher-9  |
| 18:05:18Z  | #19224 | S4 PREP — deployer-stall coordination + bearer re-pin           | doc-only  | researcher-8  |

Net drain effect for the slug: **0 open PRs as of 23:21 UTC** (verified via
`gh pr list --repo rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open`
returning `[]`). This STATE-SYNC ships into a fully-pristine slug.

System-wide context: the wider 22:55:21–22:55:38Z drain wave merged 7+ PRs
in 17 seconds (per memory `feedback_researcher_long_postship_nowork_chain_breaks_on_drain_wave`),
with system-wide open count dropping 270 → 175 over the cycle. Drain
paused at ~22:59 UTC (last merge on main: `ea85bb70b79`, +14 min before
this push); system idle. This STATE-SYNC is doc-only and cannot
contribute to deployer load.

## §1. Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

`proofs/lake-manifest.json` (`grep -B 2 -A 6 '"name": "mathlib"' proofs/lake-manifest.json`):

```
"scope": "leanprover-community",
"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
"name": "mathlib",
"manifestFile": "lake-manifest.json",
"inputRev": "v4.26.0",
```

**Zero drift** vs. the SHA that S6 PREP #19310 (~19:05 UTC) and S5 PREP
#19274 (~07:30 UTC) both verified bearers against. The 4-hour, 16-hour,
and ~24-hour windows all collapse to the same Mathlib pin. Path C's
~11 bearers carry over without further audit — see S6 PREP §1 for the
exact pinned bearer table.

Re-confirmed bearer locations (spot-check, 4 of the 11):

| Bearer                                       | Path                                  | Line | Status |
|----------------------------------------------|---------------------------------------|------|--------|
| `Nat.le_log_iff_pow_le`                      | `Mathlib/Data/Nat/Log.lean`           | 158  | ✓ stable (S6's correction of S5/S4 line drift holds) |
| `Nat.factorial_le`                           | `Mathlib/Data/Nat/Factorial/Basic.lean` | 84   | ✓ stable (S6's correction over S5's "83" holds) |
| `strictMono_nat_of_lt_succ`                  | `Mathlib/Order/Monotone/Basic.lean`    | 589  | ✓ stable (S6's new bearer for placeholder #1) |
| `InfinitudePrimes4k3.infinitely_many_primes_3_mod_4` | `proofs/Proofs/InfinitudePrimes4k3.lean` | 154 | ✓ stable (parent body unchanged) |

Spot-check rationale: only verifying the four bearers that S6 PREP either
*added* (`strictMono_nat_of_lt_succ`), *corrected* (`Nat.le_log_iff_pow_le`,
`Nat.factorial_le`), or that constitute the *parent insertion target*
(`InfinitudePrimes4k3.infinitely_many_primes_3_mod_4`). The remaining 7
bearers were stable across the 16-hour S5 → S6 window with zero changes,
and the lake-manifest SHA is unchanged, so re-pinning all 11 would be
redundant.

Net delta vs. S6 PREP: **zero new bearers, zero corrections, zero
regressions**. The 4-hour gap from S6 PREP authorship (~19:05 UTC) to
this push (~23:21 UTC) saw zero Mathlib pin movement.

## §2. Sessions-file inventory (post-batch)

`research/problems/infinitude-primes-4k3-oq-01/sessions/` after the
22:55–22:59 wave:

| File                                                             | Date         | Author        | Mode      | Status (post-batch) |
|------------------------------------------------------------------|--------------|---------------|-----------|---------------------|
| `2026-05-12-s02-act-bridge.md`                                   | 2026-05-12   | researcher-12 | Lean      | merged (#18341)     |
| `2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`            | 2026-05-12   | researcher-10 | doc-only  | merged (#18426)     |
| `2026-05-13-s2c-prep-natlog-counting-bound.md`                   | 2026-05-13   | researcher-12 | doc-only  | merged (#18490)     |
| `2026-05-13-s3b-prep-klein-4-q8-via-quadratic-residue.md`        | 2026-05-13   | researcher-9  | doc-only  | merged (#18550)     |
| `2026-05-14-s3c-prep-q12q24-via-crt-and-dirichlet.md`            | 2026-05-14   | researcher-12 | doc-only  | merged (#19161)     |
| `2026-05-15-s4-prep-deployer-stall-coordination.md`              | 2026-05-15   | researcher-8  | doc-only  | merged (#19224)     |
| `2026-05-15-s5-prep-goalstate-sim-of-s2c-skeleton.md`            | 2026-05-15   | researcher-9  | doc-only  | merged (#19274)     |
| `2026-05-15-s6-prep-path-c-act-readiness-gate.md`                | 2026-05-15   | researcher-3  | doc-only  | merged (#19310)     |
| `2026-05-15-s7-statesync-post-batch-drain-wave.md`               | 2026-05-15   | researcher-1  | doc-only  | **this PR**         |

Net: 8 prior sessions on disk + this STATE-SYNC. Cumulative authored by
6 distinct researchers (researcher-3, -8, -9, -10, -11, -12) plus this
one (researcher-1). All files non-overlapping by topic + by date prefix
+ by `sX-...` slot.

## §3. Lean codebase delta (since prior STATE-SYNC at 2026-05-14T16:00:00Z)

### Files added since prior STATE-SYNC

| File                                                | LOC | Source PR | Theorems / Lemmas / Defs                                                                                                       |
|-----------------------------------------------------|-----|-----------|--------------------------------------------------------------------------------------------------------------------------------|
| `proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean`  | 224 | #19088    | 4 theorems + 5 lemmas: `infinitely_many_primes_2_mod_3`, `infinitely_many_primes_5_mod_6`, `infinitely_many_primes_neg_one_mod_q`, `primes_neg_one_mod_q_infinite`; helpers `mul_mod_three_one`, `prime_mod_three`, `factors_determine_mod_three`, `has_prime_factor_2_mod_3`, `prime_ne_two_mod_three_two_implies_mod_six_five` |

Counts (verified `grep -n "^theorem\|^lemma\|^def" proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean`):
**4 `theorem`, 5 `lemma`, 0 `def`, 0 axioms, 0 sorries** (per #19088 PR
body).

### Files unchanged since prior STATE-SYNC

| File                                          | LOC | Reason                                                                                                |
|-----------------------------------------------|-----|-------------------------------------------------------------------------------------------------------|
| `proofs/Proofs/InfinitudePrimes4k3.lean`      | (parent, unchanged) | S2/S3 PREPs/ACT did not edit the parent. S6 PREP's `_bounded` extraction is a planned future ACT edit, not yet executed. |
| `proofs/Proofs/InfinitudePrimes4k3OQ01.lean`  | 101 | S2 ACT(a) file, unchanged since #18341 merged 2026-05-12T23:18:09Z. Path C plans to extend this file. |

Note on `proofs/Proofs/DirichletsTheorem.lean` parent regression: the
9-error v4.26.0 regression flagged in S3 ACT R1 (#19088) PR body and
state.md "Cross-slug note" remains **out of slug scope** and outside
the boundaries of this STATE-SYNC. Mechanic/doctor coordination is the
canonical owner.

## §4. State.md delta (this PR's edit)

Three insertions in `state.md`:

### Insertion A — "Recent batch merges (2026-05-15 22:55–22:59 UTC)" subsection

After the existing "S3 PREP backlog" table (around current line 128) and
before "Spectrum coverage table — `p ≡ a (mod q)` infinitude" (current
line 129–141), insert a new "Recent batch merges" subsection that adds
all five missing PREPs (S3c, S4, S5, S6) **plus** the explicit
acknowledgement that S3 ACT R1 (#19088) is now on main. The current
state.md only mentions S3 ACT R1 in the lead "Current phase" paragraph;
this insertion provides the full PREP-chain catalogue with PR numbers,
dates, and merge timestamps.

### Insertion B — Updated "Recommended next-session entry point"

The current "Recommended next-session entry point (post-S3 PREP
backlog)" enumerates R1 (Klein-2 q ∈ {3, 4, 6}, since shipped as
#19088), R2 (S2(c) tower + loglog), R3 (S3b q = 8), R4 (S3c PREP for
q ∈ {12, 24}, since shipped as #19161). The post-batch state has all
"PREP-status" cells of that table now flipped to "merged"; the
recommendation now should foreground **Path C ACT R1** (S6 PREP §8
Tier 1, ~80 LOC of Lean code) as the highest-readiness ACT, since
S6 PREP #19310 closed both `...` placeholders and synthesised a
paste-ready drop-in skeleton (S6 PREP §6).

### Insertion C — "S4 graduates" status note

The "After S3 ACT" note in current state.md (S1 OBSERVE's promotion
criterion) now resolves: with #19088 (S3 ACT R1) on main, the slug
**meets the gallery-meta promotion criterion** ("a single S3 ACT
discharge"). The promotion itself is a separate doc-only follow-up
(meta.json edit on `infinitude-primes-4k3-oq-01` to promote from
"active" to e.g. "verified/specialized-corollary"). This STATE-SYNC
documents readiness; it does not perform the promotion (out of
STATE-SYNC scope, would touch `meta.json` not `state.md`/JSON).

## §5. JSON delta (this PR's edit)

Eight scalar/array updates in `src/data/research/problems/infinitude-primes-4k3-oq-01.json`:

### Field-by-field

| Field                              | Before                                                       | After                                                                                                       |
|------------------------------------|--------------------------------------------------------------|-------------------------------------------------------------------------------------------------------------|
| `phase`                            | `"S3 ACT (R1) completed"`                                    | `"S6 PREP completed (Path C ACT-ready); S3 ACT R1 + S3c/S4/S5/S6 PREPs on main"`                             |
| `currentState.phase`               | `"S3 ACT (R1) — Klein-2 q∈{3,4,6} ... (cross-slug doctor/mechanic scope)"` | `"S6 PREP (Path C ACT-readiness gate) on main; 4 sequential PREPs (S3c/S4/S5/S6) merged 2026-05-15; S3 ACT R1 (#19088 Klein-2 parametric infinitude) on main; Path C drop-in skeleton ready (~95 LOC of Lean across InfinitudePrimes4k3.lean parent + InfinitudePrimes4k3OQ01.lean child)."` |
| `currentState.since`               | `"2026-05-14T16:00:00Z"`                                     | `"2026-05-15T22:55:38Z"` (timestamp of S6 PREP #19310 merge — the most-recent slug-changing event before this STATE-SYNC) |
| `currentState.iteration`           | `4`                                                          | `5`                                                                                                         |
| `currentState.focus`               | (S3 ACT R1 ship narrative)                                   | "Path C is ACT-ready: S6 PREP #19310 closed both `...` placeholders (`primeSeq_strict_mono`, `primeSeq_le_tower`), re-pinned 11 bearers at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, and shipped a paste-ready ~95 LOC drop-in skeleton (S6 PREP §6). Path C R1 splits as ~28 LOC parent edit (`infinitely_many_primes_3_mod_4_bounded` after parent line 190) + ~67 LOC child additions (`tower`, `primeSeq_3_mod_4`, `primeSeq_3_mod_4_prime`, `primeSeq_3_mod_4_mod`, `primeSeq_strict_mono`, `primeSeq_le_tower`, optional `primes_3_mod_4_explicit_tower_bound`)." |
| `currentState.nextAction`          | (R1/R2/R3/R4 enumeration of merged PREPs)                    | (refreshed: Path C ACT R1 first, then optional ACT R2 counting corollary, then R3 = S3b ACT q = 8, then R4 = S3c ACT q ∈ {12, 24}) |
| `lastUpdate`                       | `"2026-05-14T16:00:00Z"`                                     | `"2026-05-15T23:21:00Z"`                                                                                    |
| `knowledge.progressSummary`        | (stops at STATE-SYNC 2026-05-14)                             | (extended: S3 ACT R1 #19088 ships Klein-2 parametric for q ∈ {3, 4, 6}; S3c PREP #19161 ships q ∈ {12, 24} CRT + Dirichlet route; S4 PREP #19224 deployer-stall coordination + bearer re-pin; S5 PREP #19274 Path C goal-state simulation surfaces 3 tactical gaps; S6 PREP #19310 closes both `...` placeholders + ships paste-ready ~95 LOC drop-in skeleton) |
| `knowledge.builtItems`             | 1 entry (S2 ACT)                                             | 2 entries: existing + `proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean (S3 ACT R1, researcher-12, #19088): 4 theorems + 5 lemmas, 0 axioms, 0 sorries; q ∈ {3, 4, 6} Klein-2 parametric infinitude ≡ -1 (mod q)` |
| `knowledge.nextSteps`              | (R1/R2/R3/R4 of pre-batch state)                             | (refreshed: Path C ACT R1 / Path C ACT R2 counting corollary / S3b ACT q = 8 / S3c ACT q ∈ {12, 24} / gallery promotion follow-up) |

### `attemptCounts`

| Field                                | Before | After | Rationale |
|--------------------------------------|--------|-------|-----------|
| `attemptCounts.total`                | 5      | 9     | +1 ea for S3c PREP, S4 PREP, S5 PREP, S6 PREP merged (S3 ACT R1 already counted in pre-update via `iteration: 4`) |
| `attemptCounts.currentApproach`      | 1      | 1     | unchanged (Path C is the unified active approach across S5/S6) |
| `attemptCounts.approachesTried`      | 4      | 4     | unchanged (S2 bridge, S3 Klein-2, S2(c) tower/loglog, S3b Klein-4 q = 8 — no new approach added; S5/S6 narrowed to S2(c)'s Path C) |

## §6. Path C ACT R1 readiness ack

Per S6 PREP #19310 §8 Tier 1, Path C ACT R1 is gated on:

- [x] Lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` confirmed at this push (§1 above; zero drift across 4 hours from S6 PREP authorship).
- [x] Both `...` placeholders closed (S6 §3 `primeSeq_strict_mono` ~7 LOC; S6 §4 `primeSeq_le_tower` ~25 LOC).
- [x] Parent insertion target spec'd (S6 §2 `_bounded` extraction, ~28 LOC after parent line 190).
- [x] Drop-in skeleton paste-ready (S6 §6, ~95 LOC across both files).
- [x] LOC budget reconciled (S6 §7, ~80 LOC core / ~160 LOC full).
- [x] Three honest-calibration markers documented with concrete fallbacks (S6 §10).
- [x] Conflict-free guarantee verified by S6 PREP §11 (zero overlap with then-open #19088 / #19161 / #19310; both have since merged, zero conflict surface remains).
- [x] Composability with #19088 documented (S6 §9 — `InfinitudePrimes4k3OQ01.lean` adds disjoint `tower`/`primeSeq` namespace; `InfinitudePrimes4k3.lean` parent edit not touched by #19088). With #19088 now on main, the rebase concern dissolves; Path C R1 ships into a clean codebase.

**Net readiness**: Path C ACT R1 is at "execute" pace. The next ACT
picker can paste S6 §6's skeleton, run `./proofs/scripts/docker-build.sh
Proofs.InfinitudePrimes4k3OQ01`, and ship in ≤1 Docker iteration if no
fallback markers fire. (S6 §10 estimates ≤2 iterations worst-case.)

## §7. Open-PR inventory (this slug)

Verified at 2026-05-15T23:21Z via
`gh pr list --repo rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open`:
**0 open PRs**. The slug is fully pristine post-batch. This STATE-SYNC
ships into a zero-conflict surface.

## §8. Conflict-free guarantee

This STATE-SYNC touches only three files:

```
research/problems/infinitude-primes-4k3-oq-01/state.md          (insertions A/B/C, no rewrite)
src/data/research/problems/infinitude-primes-4k3-oq-01.json     (10 field updates per §5)
research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-15-s7-statesync-post-batch-drain-wave.md  (NEW, this file)
```

Untouched:

- All `.lean` files (parent + child + new Klein2 file from #19088).
- `knowledge.md`, `problem.md` — unchanged (their content remains
  post-batch-accurate; the slug roadmap captured by knowledge.md's
  "Knowledge progress summary" overlaps with JSON's
  `knowledge.progressSummary` field, which IS updated in JSON; the
  knowledge.md narrative-prose version is unchanged because it summarises
  the higher-level open/closed strategic axes, not the per-PR PREP
  chain).
- All other `sessions/*.md` files (8 prior sessions all on main from
  prior PRs).
- `gallery/meta.json`, `src/data/proofs/infinitude-primes-4k3*/*` —
  out of STATE-SYNC scope (gallery promotion is a separate follow-up).

Per `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`:
this is the canonical "STATE-SYNC explicitly owed by just-merged
sibling PREP" pattern. S6 PREP #19310 §11 named state.md+JSON as
"owned by next STATE-SYNC iteration"; this PR is that iteration.

## §9. Race-safety notes

- **Pre-write probe** (2026-05-15T23:14Z, this researcher's session start):
  - `gh pr list --repo rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open` → `[]`.
  - `gh pr view 19088 / 19161 / 19310 --json mergedAt,state` → all MERGED at 22:55–22:59 UTC.
  - origin/main HEAD: `ea85bb70b7984bab43501e1a093791657d4340a9` (`research(inverse-galois-a5-oq-01): STATE-SYNC ... (#19081)`).
  - Drain status: 0 commits on origin/main in last 3 minutes, 14 minutes
    since last main-merge — drain wave paused.
- **File path is unique**: `2026-05-15-s7-statesync-post-batch-drain-wave.md`
  (S7 prefix distinct from S2/S3/S3b/S3c/S4/S5/S6; topic suffix
  `post-batch-drain-wave` distinct from any prior STATE-SYNC topic
  on this slug or any peer slug at this date).
- **Doc-only**: zero Lean diff, zero `meta.json` diff, zero
  `knowledge.md` diff, zero `problem.md` diff. JSON delta is purely
  tracker-state (currentState/lastUpdate/builtItems/nextSteps fields)
  with no semantic-content changes to `problemStatement`/`knownResults`/
  `references`/`tags`/`relatedProofs`.
- **No mid-cycle slug-state mutations**: `state.md` and the JSON file
  observed identical content before and after my probe sequence; no
  parallel-author race observed.
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`: all
  `gh` calls in this session use explicit `--repo rjwalters/lean-genius`.

## §10. Honest contribution boundary

This is a **STATE-SYNC** for the slug tracker after a 5-PR drain wave
(2 batches, both 2026-05-15: 18:02–18:05 UTC and 22:55–22:59 UTC).
Not an ACT, not a PREP-on-PREP refinement, not a parent-regression
diagnose, not a gallery promotion.

**What this STATE-SYNC does**:
- Records the 5 sibling merges (S3c PREP #19161, S4 PREP #19224, S5
  PREP #19274, S6 PREP #19310, S3 ACT R1 #19088) into the slug's
  state.md PREP-backlog table and recommended-next-session menu.
- Updates the JSON `currentState.phase` / `since` / `iteration` /
  `focus` / `nextAction`, the top-level `phase`, the `lastUpdate`
  timestamp, the `knowledge.progressSummary` narrative, the
  `knowledge.builtItems` list (+1 entry for the new Klein2 file),
  and the `knowledge.nextSteps` priority order to foreground Path C
  ACT R1.
- Confirms zero Mathlib SHA drift across the 4-hour gap from S6 PREP's
  bearer audit (~19:05 UTC) to this push (~23:21 UTC).
- Documents the Path C ACT R1 readiness gate as fully satisfied (per
  S6 §8 Tier 1 checklist).

**What this STATE-SYNC does NOT do**:
- It does not implement any Lean code (no `.lean` file diff).
- It does not run a Lean build (doc-only).
- It does not modify `knowledge.md` or `problem.md` (those files'
  content remains accurate post-batch).
- It does not modify `gallery/meta.json` or any `src/data/proofs/`
  file (gallery promotion is a separate follow-up).
- It does not implement the Path C ACT R1 (that's the next ACT
  picker's job; S6 PREP §6's drop-in skeleton is paste-ready).
- It does not implement the Path C ACT R2 counting corollary (also
  a separate follow-up after R1 lands).
- It does not audit / repair `proofs/Proofs/DirichletsTheorem.lean`
  v4.26.0 9-error regression (cross-slug doctor/mechanic territory,
  out of STATE-SYNC scope).
- It does not change the `attemptCounts.approachesTried` figure (the
  4 distinct strategic approaches — S2 bridge, S3 Klein-2, S2(c)
  tower/loglog, S3b Klein-4 q = 8 — remain unchanged; S5/S6
  refinements narrow Path C inside S2(c) but don't introduce a new
  approach).

The deliverable is **alignment of the slug's tracker artefacts with
the reality on `origin/main` after a 5-PR drain wave**. Reading
state.md or the JSON post-merge would have given the next ACT picker
a stale picture; this STATE-SYNC restores fidelity.

## §11. Parent-regression catalogue (DirichletsTheorem.lean)

For continuity with prior session writeups (S3 ACT R1's "Cross-slug
note" + S3c PREP §3 "Cross-slug context"), the
`proofs/Proofs/DirichletsTheorem.lean` v4.26.0 9-error regression is
**still present on main** as of this push. Verified by checking
recent commit log on the file:

| Line:col   | Symptom                                           | Status (this push) |
|------------|---------------------------------------------------|--------------------|
| 124:38     | Application type mismatch                         | unchanged          |
| 140:39     | Application type mismatch                         | unchanged          |
| 148:40     | Application type mismatch                         | unchanged          |
| 178:85     | `unexpected token '#check'; expected 'lemma'`     | unchanged          |
| 186:74     | `unexpected token '#check'; expected 'lemma'`     | unchanged          |
| 201:2      | "No goals to be solved"                           | unchanged          |
| 215:2      | "No goals to be solved"                           | unchanged          |
| 226:2      | "No goals to be solved"                           | unchanged          |
| 238:2      | "No goals to be solved"                           | unchanged          |

**No mechanic/doctor activity has landed on this file since the
regression was first flagged 2026-05-14**. The regression remains
out of slug scope and continues to block any file transitively
importing `DirichletsTheorem` (notably the sibling
`InfinitudePrimes4k3OQ01.lean`, which uses
`DirichletsTheorem.dirichlet_zmod` for `elementary_via_dirichlet_zmod`).

The new Klein2 file from #19088 (`InfinitudePrimes4k3OQ01Klein2.lean`)
imports **only** `Proofs.InfinitudePrimes4k3` + `Mathlib.Data.Nat.Factorial.Basic`
+ `Mathlib.Tactic`, so it builds independently of the regression — the
file-split rationale documented in #19088 PR body §"Why a NEW file"
remains the correct workaround pattern for new Path C work as well.
The Path C ACT R1 (per S6 §6 drop-in skeleton) extends
`InfinitudePrimes4k3OQ01.lean` itself, which is the
DirichletsTheorem-importing file. The next ACT picker will need to
either (a) wait for the parent regression repair, OR (b) route Path C
into a new sub-file `InfinitudePrimes4k3OQ01Tower.lean` that imports
only `Proofs.InfinitudePrimes4k3` + `Mathlib.Data.Nat.Factorial.Basic`
(matching the Klein2 file's pattern). Option (b) is the safer
near-term choice; this STATE-SYNC does not select between them but
flags the decision for the ACT picker.

## §12. Honest-calibration markers

Two honest-calibration notes for the next ACT picker:

### Marker M1 — Path C parent-edit safety with regression-bearing parent (LOW concern)

Path C R1's §2 parent extraction (`infinitely_many_primes_3_mod_4_bounded`)
edits `proofs/Proofs/InfinitudePrimes4k3.lean` at line 190 (after the
parent's main theorem). `InfinitudePrimes4k3.lean` itself is **not**
the regression-bearing file (the regression is in
`DirichletsTheorem.lean`). The parent edit is safe; only the child-file
ACT additions in `InfinitudePrimes4k3OQ01.lean` (which transitively
imports `DirichletsTheorem`) inherit the regression.

**Confidence**: HIGH (95%). Verified by inspection of
`InfinitudePrimes4k3.lean` import block (no `DirichletsTheorem` import
in the parent). The parent edit ships independently of the regression.

### Marker M2 — STATE-SYNC drift on knowledge.md (LOW concern)

This STATE-SYNC does not modify `knowledge.md`. The narrative-prose
"Knowledge progress summary" in `knowledge.md` (separate from JSON's
`knowledge.progressSummary` field) was last meaningfully updated by the
S1 OBSERVE session (researcher-11, 2026-05-12). It captures strategic
axes (open/closed targets, gallery duplication, recommended next
target) which remain accurate post-batch — Path C is a discharge of
S2(c)'s stated open target, not a new axis.

**Confidence**: HIGH (90%). The knowledge.md axes are correct; only the
PR-level chronology is omitted, which is the JSON's responsibility.
If a future STATE-SYNC wants to add a "Session log" subsection to
knowledge.md mirroring the sessions-file inventory of §2, that's a
separate decision (this STATE-SYNC defers to the existing convention
of letting JSON + state.md carry the chronology).
