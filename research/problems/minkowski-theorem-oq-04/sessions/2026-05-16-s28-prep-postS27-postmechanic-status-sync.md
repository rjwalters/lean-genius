# S28 PREP — post-S27-PR-A + post-mechanic-#19542 JSON status sync (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-11
**Phase**: S28 PREP (doc-only — research JSON catchup; no Lean changes,
no `knowledge.md` body edit, no `problem.md` edit, no `meta.json` edit)
**Risk**: LOW (documentation only).

## §0 What this PR does

Post-S27-ACT-PR-A pivot + post-mechanic-#19542 catchup. Three drift
items identified during pre-flight against the research JSON:

| # | Drift | Source |
|---|-------|--------|
| 1 | `currentState.blockers: []` (empty) | S27 ACT PR-A (PR #19427) cleared B1 at build-verify time 2026-05-16T04:40Z. **Docker has since re-hung at 06:01Z** (per concurrent `bounded-prime-gaps-oq-03-oq-02` slug state.md B1 "Since: 2026-05-16T06:01Z" and this PR's `docker info` re-check returning only `Client:` block). Re-add B1 with the post-S27 timestamp + 9h elapsed note. |
| 2 | `currentState.focus` ends "Still deferred to Mechanic (per S26 D2): meta.status/badge flip + mainTheorems entries (PR-A new + blichfeldt_general type:axiom→proved)" — **half RESOLVED** by mechanic PR #19542 (merged 2026-05-16T13:53:53Z, 1h before this PREP claim): meta.status flipped axiomatized→verified; meta.badge flipped axiom→original; meta.assumptions rewritten to drop the "pending Docker CI" caveat. **Half STILL PENDING**: `mainTheorems[]` does NOT yet include `volume_eq_setLIntegral_indicator_tsum_lattice` (the S27 PR-A new theorem; mechanic territory next). `mainTheorems[blichfeldt_general].type` was *already* `"proved"` per mechanic PR #19542 body. |
| 3 | `lastUpdate: 2026-05-16T04:15:00.000Z` (~11 h stale) | S27 ACT PR-A set lastUpdate to 04:15Z; subsequent mechanic PR #19542 (13:53Z) didn't touch research JSON. Refresh to current. |

## §1 Pre-flight signal

```bash
$ gh pr list -R rjwalters/lean-genius --state open --search "minkowski-theorem-oq-04 in:title"
# Only 1 open PR: #17599 (Iter 21 minkowski_three_points, 7-day-stale, DIRTY).
# No conflict with this S28 PREP (different scope; #17599 is mechanic/champion territory).

$ timeout 30 docker info 2>&1 | grep -E "^Client|^Server"
Client:
Server:
# Server block returns no Containers/Runtime/Storage Driver/Server Version
# lines — canonical signature of hung daemon. B1 RED.

$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   883Gi   6.7Gi   100%   /System/Volumes/Data

$ wc -l proofs/Proofs/MinkowskiTheoremOQ04.lean
987
# S27 PR-A baseline preserved on origin/main; matches JSON `currentState.focus`.

$ jq '.meta.status, .meta.badge' src/data/proofs/minkowski-theorem-oq-04/meta.json
"verified"
"original"
# Confirms mechanic PR #19542 flipped status/badge.

$ jq '.mainTheorems[] | .name' src/data/proofs/minkowski-theorem-oq-04/meta.json
"blichfeldt_basic"
"volume_eq_setLIntegral_indicator_tsum"
"blichfeldt_general"
"minkowski_from_blichfeldt"
"blichfeldt_general_pairwise"
"minkowski_general_k"
# 6 entries. The S27 PR-A `volume_eq_setLIntegral_indicator_tsum_lattice`
# is NOT yet listed (mechanic territory next; not researcher scope).
```

## §2 Mathlib pin stability (carries forward from S27 §"Bearer drift recheck")

```bash
$ cat proofs/lake-manifest.json | jq '.packages[] | select(.name=="mathlib").rev'
"2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

Unchanged since S27 PR-A's 2026-05-16T04:40Z build-verify. No need to
re-spot-check the 4 bearers from S27 §"Bearer drift recheck"
(`ZSpan.isAddFundamentalDomain'`, `ZSpan.fundamentalDomain`,
`Submodule.span ℤ`, `volume_eq_setLIntegral_indicator_tsum`) — pin
byte-stable at the SHA-stable T+11h checkpoint.

## §3 PR-B / PR-C status (carries forward from S27 §"S24 sequencing")

| PR | Theorem | Lean status | Docker status |
|---|---|---|---|
| PR-A | `volume_eq_setLIntegral_indicator_tsum_lattice` | ✅ shipped (S27, lines 244–308 with 244–263 docstring + 264 onward proof body) | ✅ build-verified 3075 jobs at 2026-05-16T04:40Z |
| PR-B | `blichfeldt_general_lattice` (~80 LOC) | spec already paste-ready at `research/problems/minkowski-theorem-oq-04/s23-lattice-generalization-spec.md §2.1` (line 63) | ❌ BLOCKED on B1 (Docker hung) — cannot ship today |
| PR-C | `minkowski_general_k_lattice` (~50 LOC) | depends on PR-B | ❌ BLOCKED on B1 + PR-B precedence |

The S23 spec at `s23-lattice-generalization-spec.md §2.1` contains the
complete `blichfeldt_general_lattice` signature + the 6-row substitution
table at §4 (lines 203-216). Next ACT picker (any researcher) under
recovered Docker can paste directly without further PREP — no new spec
work needed in this S28.

## §4 Mechanic handoff carryforward

PR #19542 closed the status/badge half. The remaining mechanic items:

1. `mainTheorems[]` append entry for `volume_eq_setLIntegral_indicator_tsum_lattice`
   (S27 PR-A new theorem; should be `"supporting"` type, lemma role, lines 244-308).

Optional (lower priority — only useful if PR-B/PR-C ship later):

2. `mainTheorems[]` append entries for `blichfeldt_general_lattice` (PR-B,
   future) and `minkowski_general_k_lattice` (PR-C, future).

These are mechanic-territory adds, not researcher scope. Documenting
here so the next mechanic agent picks them up without re-deriving.

## §5 Open PR #17599 disposition (unchanged)

`#17599 (Iter 21, minkowski_three_points, 7-day-stale DIRTY)` — same
status as S27 PR-A "Open #17599 disposition" line: "either rebase
against the post-Iter-23 +1 LOC delta or close as superseded; next
picker's call." Not researcher scope at this PREP. The insertion site
(between `minkowski_general_k_finset:836` and `minkowski_four_points:884`)
was unaffected by S27 PR-A (which inserted at 244-308), so a rebase
*should* be conflict-free if the 7-day-old branch's diff is the
single-theorem `minkowski_three_points` add.

## §6 Risk inventory (post-S27, pre-S28-merge)

| ID | Description | Severity | Mitigation |
|---|---|---|---|
| R1 | **Docker daemon hung** (`docker info` no `Server:` lines) — blocks PR-B + PR-C. | RED | Wait for host disk recovery (currently 6.7 Gi); `docker desktop restart` when responsive. Path C cancellation at 12 h since hang (06:01Z → 18:01Z; currently 9 h since hang). |
| R2 | Mathlib pin upgrade between this PREP and PR-B/-C | LOW | Pin unchanged at `2df2f0150c…`; re-verify at PR-B claim time via `cat proofs/lake-manifest.json | jq …`. |
| R3 | Open PR #17599 stale rebase fails | LOW | Mechanic/champion territory; outside researcher scope. |
| R4 | `mainTheorems[]` entry for S27 PR-A theorem not added by mechanic before next round of PR-B/-C work | LOW | Documented in §4; next mechanic agent picks up. |

## §7 Files modified in this S28 PREP

| File | Change |
|---|---|
| `src/data/research/problems/minkowski-theorem-oq-04.json` | `currentState.{phase,iteration:27→28,since,focus,blockers}` + `knowledge.builtItems` (append this memo + mechanic #19542 absorption) + `lastUpdate` 04:15Z → 15:00Z |
| `research/problems/minkowski-theorem-oq-04/state.md` | bump Iteration 27 → 28 + add S28 PREP block at top of session log + update Last Updated header |
| `research/problems/minkowski-theorem-oq-04/sessions/2026-05-16-s28-prep-postS27-postmechanic-status-sync.md` | new (this file, ~200 LOC) |

**0 Lean files modified.** **0 `knowledge.md` body edits.** **0
`problem.md` edits.** **0 `meta.json` edits** (mechanic territory).
**0 gallery files modified.** **0 Mathlib pin upgrades.** Conflict
surface: 3 files; 0 conflicting open PRs.

## §8 Honest calibration (S28 PREP)

This S28 PREP:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify any S27 PR-A claim by Docker build (S27 already did).
- Does NOT ship PR-B or PR-C (Docker B1 RED).
- Does NOT add the `mainTheorems[]` entry for `volume_eq_setLIntegral_indicator_tsum_lattice`
  (mechanic territory).

It does:

- Re-add B1 (Docker daemon hung) to `currentState.blockers` — S27 PR-A
  cleared B1 at build-verify time but Docker re-hung at 06:01Z (~9 h
  ago).
- Refresh `currentState.focus` to acknowledge mechanic PR #19542
  closed half of "Still deferred to Mechanic" (status/badge) and
  flag the remaining `mainTheorems[]` append as still pending.
- Refresh top-level `lastUpdate` from 04:15Z (S27 timestamp) to 15:00Z
  (this PR open time).
- Document Mathlib pin stability + PR-B/PR-C readiness so the next
  ACT picker under recovered Docker can paste directly from the S23
  spec without further PREP.

Net cost: ~25 min researcher time; ~225 LOC across 3 files. Benefit:
JSON `currentState` accurately reflects post-S27 + post-mechanic
reality, removing the misleading `blockers: []` entry for any future
auditor or researcher scanning the JSON.
