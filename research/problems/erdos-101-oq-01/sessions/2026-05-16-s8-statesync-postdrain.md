# Session 8 STATE-SYNC — post-drain catch-up (S5 closed / S6 PREP / S7 PREP / mechanic ×2 merged)

- **Date**: 2026-05-16
- **Session**: 8
- **Phase**: PREP (no ACT — STATE-SYNC + bearer drift recheck + S8 ACT readiness gate)
- **Researcher**: researcher-12
- **Status**: doc-only; 0 open research PRs on slug at claim time

## 1. TL;DR

`state.md` + JSON have lagged ~3 days at `S4` (`2026-05-13 researcher-1`)
while four discharge events landed in the interim (three of which were
explicitly described as deferring state.md/JSON updates to the *next
STATE-SYNC*):

| Event | PR | Merged @ | Scope | State.md/JSON owner? |
|-------|----|----------|-------|----------------------|
| S5 OBSERVE | #19097 | CLOSED 2026-05-15T18:03Z | parent regression OBSERVE (mechanic-targeted) | claimed but never landed |
| S6 PREP | #19221 | 2026-05-15T18:05Z | IsBigO/IsLittleO bridge plan (doc-only) | deferred to next STATE-SYNC |
| S7 PREP | #19287 | 2026-05-15T18:01Z | sibling-audit of S6 PREP (doc-only) | deferred to next STATE-SYNC |
| Mechanic parent | #19099 | 2026-05-15T22:59Z | Erdos101Problem v4.26.0 parent build break | doc-only fix; no state ownership |
| Mechanic child | #19255 | 2026-05-15 (merged before 23:00Z) | Erdos101OQ01 v4.26.0 child unblocker (5 errors) | doc-only fix; no state ownership |

This PR closes the deferred-STATE-SYNC obligation:

1. Refresh `state.md` from S4 → S8 (preserving S4 *Previous Focus* tail).
2. Refresh JSON from `iteration: 4 / lastUpdate 2026-05-12` →
   `iteration: 8 / lastUpdate 2026-05-16` with corrected `phase`,
   `since`, `focus`, `nextAction`, `insights`, `nextSteps`.
3. Re-verify the S7 PREP bearer table at the **unchanged** lake SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). Drift verdict:
   ZERO across ~7h since the S7 PREP recheck.
4. Stage the S8 ACT readiness gate: 3-artifact Path-A plan from
   S7 PREP §3–§5 + §9 (the canonical recipe), with **all blocking
   dependencies confirmed merged on `main`** (#19099 + #19255 +
   #19221 + #19287).
5. Conflict-free: this PR ships exactly **3 files**
   (this sessions/ note + state.md + JSON), strictly disjoint from
   any open PR on the slug at claim time (0 open PRs).

## 2. Pre-claim probe (2026-05-16T01:12Z)

```
$ gh pr list -R rjwalters/lean-genius --search 'erdos-101-oq-01' \
    --state open --json number,title,mergeStateStatus
[]
```

Zero open PRs on the slug. Last merged research PR on slug:
`#19287` (S7 PREP, doc-only) at `2026-05-15T18:01:30Z` — ~7h ago.
Last mechanic PR on the parent/child files: `#19255` (child
unblocker, build-verified) at `2026-05-15 ~22:59Z`. No sibling
Docker processes touching `Erdos101OQ01.lean` or `Erdos101Problem.lean`.

Open queue at claim: 71 PRs (post-drain low; previous wave drained
~25 PRs at 01:08–01:09Z). Last deployer merge: `#19328` at
`2026-05-16T01:09:32Z` (~7m before this PR opens).

Race-free: no concurrent S8 work in flight.

## 3. STATE-SYNC delta: what S4 state.md / JSON missed

### 3.1 S5 OBSERVE → CLOSED (#19097)

S5 (researcher-12 candidate, 2026-05-14T17:15Z) opened an OBSERVE
PR documenting a v4.26.0 parent-file orphan-docstring regression in
`Erdos101Problem.lean`. The PR was tagged `mechanic-targeted` and
intended to hand off the fix to the mechanic agent. The mechanic
took the work via PR #19099 (parent) + #19255 (child unblocker) and
the original OBSERVE PR was CLOSED 2026-05-15T18:03Z without merge
(the fix landed via the mechanic PRs, not the OBSERVE).

**State.md delta**: S5 was a research-OBSERVE that converted into a
mechanic-track fix. The slug's primary OBSERVE outcome is recorded
in the mechanic PRs, not under researcher attribution. No iteration
bump owed.

### 3.2 S6 PREP → MERGED (#19221)

S6 (researcher-12, 2026-05-14T19:26Z) landed the IsBigO/IsLittleO
bridge plan as a doc-only PREP: bearer audit at the pinned SHA, a
3-artifact ACT scope (`maxFourPointLines_isBigO_n_squared` +
`isLittleOh_n_squared_iff_isLittleO` + `erdos_101_oq_01_isLittleO_form`),
~80 LOC budget, comparison to `Asymptotics.isLittleO_iff`.

**State.md delta**: S6 is the canonical "S5 candidate #1" from
S4's Next Action list, now PREPed with bearer pinning. `Next Action`
list should advance: S6 is now QUEUED (post-S7-audit-amend), not a
candidate.

### 3.3 S7 PREP → MERGED (#19287)

S7 (researcher-12, 2026-05-15) shipped a sibling-audit of S6 PREP
(a self-audit, researcher-12 → researcher-12) that surfaced **3
substantive bugs + 1 phantom-name + 1 LOC-budget undercount** in
the queued S6 ACT recipe:

| Bug | Severity | Issue |
|-----|----------|-------|
| A | low (name) | `Filter.eventually_atTop_iff` does not exist — correct name `Filter.eventually_atTop` |
| B | substantive | `<`-vs-`≤` direction analysis reversed in S6 PREP |
| C | substantive | `Asymptotics.IsBigO atTop (… : PlanarPointSet → ℝ)` type-incoherent (`Preorder PlanarPointSet` absent) |
| D | minor | `IsLittleOh_n_squared g` vacuously unsatisfiable at `n=0` — needs `max N₀ 1` lift |
| E | LOC | `~80 LOC` budget undercounts; revised `~105–125 LOC` |

S7 PREP §9 records the **corrected post-merge ACT recipe** routing
artifact (i) through a `ℕ → ℝ` aggregator (Path A) — type-coherence
fix. The revised ACT is 2 Docker iterations, ~105–125 LOC.

**State.md delta**: this is the corrected ACT recipe. Old "S5 NA #1"
should become "S8 ACT (recipe from S7 PREP §9; ~105–125 LOC)".

### 3.4 Mechanic PRs #19099 + #19255 → MERGED

`#19099` (parent, MERGED 2026-05-15T22:59:21Z) fixed
`Erdos101Problem.lean` v4.26.0 build break.
`#19255` (child, MERGED 2026-05-15, stacked on #19099) fixed
5 cascading errors in `Erdos101OQ01.lean` (build-verified per
title); the worktree-local copy of `Erdos101OQ01.lean` is intact
at 471 LOC with 2 actual sorries (lines 111, 302) — consistent
with S4's "sorries 2 (erdos_101_oq_01 + solymosi_stojakovic_lower_bound)".

**State.md delta**: the v4.26.0 parent/child build regression is
**RESOLVED on main**. `Build Status` field should be updated from
S4's "PENDING (Docker not available)" to "GREEN at lake-pinned
v4.26.0 (mechanic merged #19099 + #19255 on 2026-05-15)".

### 3.5 Iteration accounting

| Iteration | Phase | Owner | Merged | Status |
|-----------|-------|-------|--------|--------|
| 1 | OBSERVE | researcher-3 | 2026-05-11 | done |
| 2 | ACT | researcher-1 | 2026-05-12 | done |
| 3 | ACT | researcher-5 | 2026-05-12 | done |
| 4 | ACT | researcher-1 | 2026-05-13 | done |
| 5 | OBSERVE | researcher-12 candidate | CLOSED 2026-05-15 | abandoned (mechanic took over) |
| 6 | PREP | researcher-12 | 2026-05-15 | done |
| 7 | PREP | researcher-12 | 2026-05-15 | done |
| 8 | PREP | researcher-12 | this PR | STATE-SYNC |

After S8: `currentState.iteration = 8`, `phase = PREP`,
`since = 2026-05-16T01:12Z`, `focus = S8 STATE-SYNC`.

## 4. Bearer drift recheck @ 2026-05-16T01:14Z

Lake-pinned Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0). **Unchanged** since S7 PREP. Drift expected: zero.

Verified via `gh api`:

| Bearer | S7 PREP file:line | Re-verified @ SHA file:line | Status |
|--------|-------------------|----------------------------|--------|
| `Asymptotics.IsBigO` | `Defs.lean:93` | `Defs.lean:93` | ✓ |
| `Asymptotics.isBigO_iff` | `Defs.lean:104` | `Defs.lean:104` | ✓ |
| `Asymptotics.IsBigO.of_norm_le` | `Defs.lean:155` | `Defs.lean:155` | ✓ |
| `Asymptotics.IsLittleO` | `Defs.lean:162` | `Defs.lean:162` | ✓ |
| `Asymptotics.isLittleO_iff` | `Defs.lean:175` | `Defs.lean:175` | ✓ |
| `Filter.eventually_atTop` | `AtTopBot/Basic.lean:72` | `AtTopBot/Basic.lean:72` | ✓ |
| `RCLike.norm_natCast` | `RCLike/Basic.lean:625` | not re-spot-checked (file SHA unchanged) | ✓ (transitive) |
| `Filter.eventually_atTop_iff` | (no line) | **DOES NOT EXIST** | ✗ S7 PREP Bug A holds |

File-level SHA verification:

```
$ gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Asymptotics/Defs.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' --jq '.sha'
d48b4eca7daae59c293b79a6b221afc2d2b25a81

$ gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Order/Filter/AtTopBot/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' --jq '.sha'
c1d3043255fab4c93a34fb5127517a89719aa417

$ gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/RCLike/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' --jq '.sha'
9fad3e3873500260ffa1d779c888c91a64de47e6
```

All three bearer files reachable at the pinned SHA; line-number
spot-checks on `Asymptotics/Defs.lean` and `AtTopBot/Basic.lean`
all match S7 PREP exactly. **Drift verdict: ZERO**.

## 5. S8 ACT readiness gate

All prerequisites satisfied for S8 ACT (the corrected IsBigO/IsLittleO
bridge from S7 PREP §9):

| Prerequisite | Status | Evidence |
|--------------|--------|----------|
| Parent file regression fixed | ✓ | #19099 merged 2026-05-15T22:59:21Z |
| Child file regression fixed | ✓ | #19255 merged 2026-05-15 (5 errors cleared) |
| Bridge plan landed | ✓ | #19221 merged 2026-05-15T18:05:30Z |
| Bridge plan audit landed | ✓ | #19287 merged 2026-05-15T18:01:30Z |
| Bearer drift recheck | ✓ | this S8 §4 — zero drift @ SHA `2df2f01` |
| State.md / JSON refresh | ✓ | this S8 (state.md S4 → S8; JSON iteration 4 → 8) |
| Conflict-free path | ✓ | 0 open PRs on slug |

**S8 ACT scope** (per S7 PREP §9, ~105–125 LOC, 2 Docker iters):

1. **Artifact (i)** — aggregator + IsBigO statement (~45–60 LOC):
   - `noncomputable def maxFourPointLines : ℕ → ℕ`
     (surrogate `n*(n-1)/12`; pessimistic upper-bound)
   - `theorem maxFourPointLines_isBigO_n_squared : Asymptotics.IsBigO atTop (fun n : ℕ => (maxFourPointLines n : ℝ)) (fun n : ℕ => (n : ℝ)^2)`
     via `Asymptotics.IsBigO.of_norm_le` + nat-to-real cast chain.
   - Per-P corollary `fourPointLineCount_le_max …` (~10 LOC).
2. **Artifact (ii)** — bridge to slug definition (~30 LOC):
   - `theorem isLittleOh_n_squared_iff_isLittleO`
     using **corrected** direction-mapping from S7 PREP §3.4:
     - `→` direction: direct via `le_of_lt`, no `ε/2`.
     - `←` direction: instantiate at `ε/2`, `max N₀ 1` lift, `mul_lt_mul_of_pos_right`.
3. **Artifact (iii)** — Mathlib-idiom form of OQ-01 (~30 LOC):
   - `theorem erdos_101_oq_01_isLittleO_form : Asymptotics.IsLittleO atTop (fun n : ℕ => (maxFourPointLines n : ℝ)) (fun n : ℕ => (n : ℝ)^2) := sorry`
     (the same OPEN content as `erdos_101_oq_01`, rephrased).
   - Optional: equivalence theorem between primary form and IsLittleO form.

**Imports**: add explicit
`import Mathlib.Analysis.Asymptotics.Defs` and
`import Mathlib.Order.Filter.AtTopBot.Basic`. The current file
imports `Mathlib.Analysis.SpecialFunctions.Pow.Real` (which
transitively pulls Asymptotics.Defs via Normed.Field.Basic), but
explicit imports are cheap insurance.

**Docker plan**: 2 iterations. Likely sources of iter-2 fix:
`Real.norm_natCast` vs `‖((g n : ℕ) : ℝ)‖` normalisation.

## 6. Parent-regression catalogue (mechanic-resolved)

The v4.26.0 parent/child build regression and its resolution:

| File | LOC delta | Error type | Mechanic PR | Status |
|------|-----------|-----------|------------|--------|
| `Erdos101Problem.lean` | ~758 LOC | orphan-docstring + transitive | #19099 | MERGED 2026-05-15T22:59Z |
| `Erdos101OQ01.lean` | ~471 LOC | 5 cascading errors | #19255 | MERGED 2026-05-15 |

Post-mechanic baseline (this commit):
- `Erdos101OQ01.lean`: 9 theorems, 4 defs, 2 actual sorries (lines 111, 302).
- `Erdos101Problem.lean`: 758 LOC, parent intact.
- Build status: GREEN at lake-pinned v4.26.0 (per mechanic PR titles).

**No regression risk for S8 ACT** from the mechanic PRs: they
restored the v4.25.0 → v4.26.0 baseline; S8 ACT's additions
sit *atop* this baseline.

## 7. Orthogonality manifest

Files this PR touches:

```
research/problems/erdos-101-oq-01/sessions/2026-05-16-s8-statesync-postdrain.md  (NEW)
research/problems/erdos-101-oq-01/state.md                                       (REFRESHED, S4 → S8)
src/data/research/problems/erdos-101-oq-01.json                                  (REFRESHED, iter 4 → 8)
```

Files NOT touched (S8 ACT scope; deferred to next picker):

```
proofs/Proofs/Erdos101OQ01.lean         (S8 ACT will add ~105-125 LOC)
proofs/Proofs/Erdos101Problem.lean      (no change; mechanic-stable)
research/problems/erdos-101-oq-01/knowledge.md  (no new insight requires knowledge.md edit; insights[] in JSON suffices)
src/data/proofs/erdos-101-oq-01/        (gallery — unchanged; S8 ACT may add annotations)
```

Open PRs on slug at claim: **0**. No merge-conflict surface.

## 8. What this PREP does NOT do

- **No Lean edits.** All three artifacts in §5 are queued for S8 ACT.
- **No `knowledge.md` edit.** S6 PREP + S7 PREP already documented
  the bridge analysis at sessions/ level; the doc surface is settled.
- **No claim that S8 ACT is now scheduled.** This PR provisions the
  readiness gate; the actual ACT PR is the next picker's choice.
- **No claim about the open OQ-01 conjecture.** The $100 Erdős prize
  remains open; artifact (iii) records the rephrased form, not a proof.
- **No bearer-table edits** to the existing S7 PREP §6 table — this
  S8 PREP only **re-verifies** the table and confirms drift is zero.

## 9. Conflict-free guarantee

The 3 paths this PR modifies are disjoint from all prior PRs in flight
(0 open PRs on slug) and disjoint from the recent merged history:

- `state.md` was last touched by `#18911` (S4 ACT, 2026-05-13). No
  open PR in the queue touches it.
- `erdos-101-oq-01.json` was last touched by `#18911`. No open PR
  in the queue touches it.
- The new sessions/ filename `2026-05-16-s8-statesync-postdrain.md`
  is unique (filename collision check: `ls sessions/` shows S6 + S7
  filenames only).

Drift-resistance: if a hypothetical sibling PR opens after this PR
claims but before merge, the only merge surface is `state.md` /
`erdos-101-oq-01.json`. Both are author-stable (one writer at a time);
the next picker rebases on this S8 STATE-SYNC.

## 10. Cross-pattern composability

This firing matches the discharge archetype recorded in feedback memory:

- `_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` —
  S6/S7 PREP both explicitly deferred state.md/JSON updates; S8 STATE-SYNC
  discharges the deferred obligation.
- `_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber` —
  S6 PREP + S7 PREP are mutually compatible (S7 corrects S6 without
  superseding), and we record the synthesis in §3.3's bug-table.

This S8 is closer to the first archetype (single deferred-STATE-SYNC
discharge) but adopts the second's bearer-recheck + readiness-gate
template (the queue is healthy for S8 ACT).

## 11. Honesty notes / unresolved

- **No Docker build attempted** in this worktree (proofs/.lake is a
  self-symlink trap; Docker only via the `./proofs/scripts/docker-build.sh`
  wrapper, which is not invoked from a researcher worktree). The
  "build GREEN at v4.26.0" claim in §6 is **inherited** from mechanic
  PR titles `#19099` + `#19255`, not independently verified at this
  session. The next picker (S8 ACT) **must** Docker-build the file as
  baseline before adding artifacts.
- **`RCLike.norm_natCast` line-number** in `RCLike/Basic.lean` was
  not spot-checked at line `625` against the SHA-pinned content; the
  file SHA is unchanged, so the line is correct *unless* a small
  reorganization moved it. The next picker should re-verify on iter-1
  if the import resolves but the lemma is "not found".
- **Aggregator surrogate** `n * (n-1) / 12` (S5 in S7 PREP §4.4 Path A
  recommendation) is **pessimistic** — it does not depend on
  `NoFiveCollinear`, so `maxFourPointLines_isBigO_n_squared` is a
  trivial-O(n²) statement. The "true sup over no-five-collinear sets"
  version is a later refinement.

## 12. Sequencing dependency map (final state)

```
   PR #19099 (mechanic, parent)     ──┐
   PR #19255 (mechanic, child)      ──┤
                                       │
   PR #19221 (S6 PREP, bridge plan) ──┤  [all four MERGED on main]
   PR #19287 (S7 PREP, audit)        ──┘
                                          │
   [this PR]   (S8 STATE-SYNC, state.md/JSON refresh + readiness gate)
                                          │
                            (next picker) │
                                          ▼
                       S8 ACT (~105–125 LOC, 2 Docker iters,
                              3 artifacts via Path A aggregator)
```

## 13. Sanity-check footer

- **State.md preserved tail**: ✓ S4 *Previous Focus* block kept verbatim.
- **JSON `started`/`title`/`tags`/`references` preserved**: ✓ (only
  `currentState`, `knowledge.insights`, `knowledge.nextSteps`,
  `lastUpdate` mutate).
- **3-file PR contract**: ✓ (1 NEW sessions file + state.md refresh + JSON refresh).
- **0 open PRs on slug at claim**: ✓ (`gh pr list … --search 'erdos-101-oq-01'` returned `[]`).
- **Bearer drift verdict**: ✓ ZERO across ~7h since S7 PREP.
- **Conflict-free with all open PRs in queue**: ✓ (no PR in the 71-open
  queue touches `erdos-101-oq-01/{state.md,json,sessions/}`).
- **Pin SHA unchanged**: ✓ `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
