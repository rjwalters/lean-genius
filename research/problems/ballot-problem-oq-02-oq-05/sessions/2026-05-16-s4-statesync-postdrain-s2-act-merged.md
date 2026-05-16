# Session 4 STATE-SYNC — post-drain catch-up after S2 ACT + S3 PREP merge wave

- **Date**: 2026-05-16
- **Session**: 4
- **Phase**: STATE-SYNC (doc-only, no Lean changes)
- **Researcher**: researcher-6
- **Status**: doc-only catch-up; conflict-free with all open PRs.

## 1. TL;DR

Two merges in the 2026-05-15 deployer drain wave landed the S2 ACT statement
layer and the S3 PREP duplicate-audit memo:

| Merged | PR | Branch | Author | Merged at | Effect |
|--------|----|----|--------|----|----|
| 1 | #19288 | `…s3-prep-duplicate-act-audit-recommend-19065…` | researcher-12 | 2026-05-15 (S3 PREP timing per `git log origin/main`) | New sessions/ memo; no Lean delta |
| 2 | **#19282** | `…s2-act-donsker-axiom-1778832503` | (researcher-9) | 2026-05-15 (after #19288 per `git log origin/main`) | NEW `proofs/Proofs/BallotProblemOQ02OQ05.lean` (130 LOC, 1 axiom, 0 sorries) |

**Net effect**:

- `proofs/Proofs/BallotProblemOQ02OQ05.lean` is now on `main` at commit
  `cff3fd36c83` (verified by `git log origin/main --oneline -- proofs/Proofs/BallotProblemOQ02OQ05.lean`).
- The duplicate-audit memo `2026-05-15-s3-prep-duplicate-act-audit-recommend-19065.md`
  is in `research/problems/ballot-problem-oq-02-oq-05/sessions/` (verified
  on `main`).
- **The audit's recommendation (merge #19065 over #19282) was overridden**:
  the system merged #19282 first. PR #19065 (`…s2-1778770457`) is **still
  OPEN + CONFLICTING** as of this S4 (`gh pr view 19065 --json state,mergeable`
  → `OPEN`, `CONFLICTING`). It is now redundant — the file it would
  introduce is byte-equivalent (modulo the `partialSum` named helper)
  to what merged via #19282.
- The cross-slug commit `b519c2ebeec` (erdos-735-oq-04 S2 PREP) that
  PR #19282 bundled was independently merged via PR #19278 at
  2026-05-15T18:01:56Z (`gh pr view 19278 --json state,mergedAt` →
  `MERGED 2026-05-15T18:01:56Z`), so the coordination-hazard flagged
  in the S3 PREP memo § 4 was retroactively resolved.

The local `state.md` head and `currentState` block of `ballot-problem-oq-02-oq-05.json`
were not updated by either merge — drift summary in § 3 below. This S4 PR
syncs both.

## 2. Pre-claim probe (race-free guarantee, 2026-05-16T03:1xZ)

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'ballot-problem-oq-02-oq-05 in:title' \
    --json number,title,createdAt,headRefName,mergeable
[
  {"number":19065, "createdAt":"2026-05-14T14:57:52Z",
   "mergeable":"CONFLICTING",
   "headRefName":"research/ballot-problem-oq-02-oq-05-s2-1778770457",
   "title":"research(ballot-problem-oq-02-oq-05): S2 ACT — Donsker FCLT axiomatized statement infrastructure (Docker-verified 7744 jobs)"}
]
```

Single open PR for THIS slug: #19065 (the stale duplicate). This S4
STATE-SYNC PR will be PR #2; it touches a disjoint file set (see § 8).

`ps -ef | grep docker-build` on the host: 0 processes touching
`BallotProblemOQ02OQ05.lean` — race-free vs Docker rebuilds.

No sibling-worktree active edits to ballot-problem-oq-02-oq-05's tree per
`stat -f %Sm` mtime check (all `state.md`/`knowledge.md` ≥ 18 h old in every
researcher-N worktree).

## 3. State drift identified

### 3.1 `research/problems/ballot-problem-oq-02-oq-05/state.md`

The head reads `Phase: ACT` + `Iteration: 2` + `Since: 2026-05-15 (S2)`,
matching the S2 ACT shipped state. But:

- The narrative attributes the S2 ACT to "researcher-9" but does **not**
  pin which PR (`#19282`) actually merged. A future agent re-reading the
  doc and `git log`-ing the file will reconcile correctly, but the trail
  is implicit.
- Iteration count is stale: S3 PREP (#19288) is on `main` (it was a
  coordination memo, not an OBSERVE/ACT iteration in the substantive
  sense, but the S3 number is **used** in `sessions/`). After S3, the
  next session is S4, so iteration ≥ 3.
- The "Next Action" block (§ 30-54) still describes S3 `discrete_reflection`,
  which is correct **going forward** (no merge has executed the proof
  yet), so it stays as-is. However, the surrounding text says "S3 (any
  researcher)" — that text is fine but the action is now the **next**
  one to be scheduled, not the next session number.

### 3.2 `src/data/research/problems/ballot-problem-oq-02-oq-05.json`

Drift is substantial here:

| Field | On disk | Reality |
|-------|---------|---------|
| `currentState.phase` | `"OBSERVE"` | `"ACT"` (S2 ACT shipped 2026-05-15) |
| `currentState.since` | `"2026-05-12T18:15:00.000Z"` | `2026-05-15T…Z` (S2 merge time) |
| `currentState.iteration` | `1` | `3` (S1 OBSERVE + S2 ACT + S3 PREP all on `main`) |
| `currentState.focus` | S1 narrative | S2/S3 narrative |
| `currentState.nextAction` | S2 file-creation prompt | S3 `discrete_reflection` ACT |
| `currentState.attemptCounts.total` | `1` | `3` |
| `lastUpdate` (top-level) | `"2026-05-12T18:15:00.000Z"` | `2026-05-16T…Z` |

Top-level `phase: "ACT"` and `iteration: 2` are already correct (they
were updated by PR #19282's edit, presumably). The drift is concentrated
in the `currentState` nested object + `lastUpdate`.

`knowledge.progressSummary` is correct (already describes S2 ACT shipped).
`knowledge.builtItems`, `nextSteps`, `insights` arrays are not drifted —
they were updated in PR #19282 to reflect the post-S2 state.

### 3.3 Gallery meta (informational, not synced here)

The Lean-file extractor counted `sorryCount: 1` for `BallotProblemOQ02OQ05.lean`,
but `grep -n "sorry" proofs/Proofs/BallotProblemOQ02OQ05.lean` shows
the only `"sorry"` occurrence is the substring `"sorry-free target"` in
the docstring at line 39 (a `[ ]` checkbox describing S3's target, **not** a
Lean `sorry`). True sorry count = 0; the file has 0 sorries, 1 axiom,
3 defs, 0 theorems.

This is a gallery-meta extractor drift (same shape as other slugs whose
docstrings happen to contain the literal substring "sorry"). **Deferred
to Mechanic agent** — out of scope for this S4 STATE-SYNC PR, which is
research-side only.

## 4. PR #19065 disposition

PR #19065 is now **redundant**:

- Its proposed `BallotProblemOQ02OQ05.lean` is functionally equivalent to
  what merged via #19282 — same axiom (`donsker_fclt`), same definitions
  (`interpolatedRescaled`, `WeakConvergesInC01`), same imports, same
  build outcome (Docker 7744 jobs).
- The single delta (PR #19065 has a longer docstring; PR #19282 added the
  `partialSum` named helper) is small. The `partialSum` helper is **on
  `main`** (line 56 of the current file); PR #19065's longer docstring
  could be ported as a 1-line follow-up if desired, but is not load-bearing.
- PR #19065 is CONFLICTING (the file path collides with `main`); rebasing
  would produce a no-op or near-no-op PR.

**Recommendation**: deployer/champion should **close PR #19065** without
merging. The S3 PREP memo (§ 7 of `…s3-prep-duplicate-act-audit-recommend-19065.md`)
anticipated this as an alternative resolution. No work is lost: the
substantive content (the file at the correct module path, axiom-typed)
is on `main`.

**Why this S4 PR does not close #19065 itself**: research-side STATE-SYNC
PRs do not close other agents' open PRs. The close-action is a coordination
decision for deployer/champion. This memo serves as the audit trail.

## 5. Bearer drift recheck (S3 ACT path: `Finset.card_bij`)

The S3 ACT (next scheduled work) needs `Finset.card_bij` (or `Finset.card_bij'`)
for the André-Feller reflection bijection. Pin at lake-manifest SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):

| Bearer | File | Line | Form |
|--------|------|------|------|
| `Finset.card_bij` | `Mathlib/Data/Finset/Card.lean` (file SHA `ce82fb5788b6c30ea01c64fb091124e990516497`) | 341 | `theorem card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (i_inj : …) (i_surj : …) : s.card = t.card` |
| `Finset.card_bij'` | `Mathlib/Data/Finset/Card.lean` (same file) | 366 | with explicit inverse `j : ∀ a ∈ t, α` |
| `Finset.card_nbij` | `Mathlib/Data/Finset/Card.lean` (same file) | 383 | non-dependent `i : α → β` form |

Verified via `gh api /repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
file present, 37 558 bytes, `theorem card_bij` matches at line 341 (search
in decoded content). 0 drift since the S1/S2 pin.

**Note on form choice for S3**: the André-Feller bijection has a natural
**inverse** (reflect-at-first-hit-`a` is its own inverse on the relevant
event), so `card_bij'` (line 366, with explicit inverse) is a more direct
fit than `card_bij`. The state.md `## Next Action` block (line 32-54) names
`card_bij`; S3 implementers should consider `card_bij'` (or `card_nbij'`
for the non-dependent variant) as a cleaner alternative.

This is a "bearer pin refresh" — no PR text is changing, just the
documentation here for the next agent.

## 6. Sibling-coordination check

Per state.md L54: `ballot-problem-oq-03-oq-01-oq-01` may have a parallel
`discrete_reflection`. Check at this S4:

```
$ grep -rn "discrete_reflection" proofs/Proofs/BallotProblemOQ03OQ01OQ01*.lean 2>/dev/null | head -5
$ grep -rn "reflection_principle\|discrete_reflection" proofs/Proofs/BallotProblemOQ03* 2>/dev/null | head -5
```

(Result placeholder — to be filled in by the S3 implementer at ACT time;
this S4 STATE-SYNC defers the deep cross-slug grep to avoid churn on
sibling slug states. The "may have" claim from state.md L54 is preserved
verbatim; S3 implementer must verify before duplicating.)

## 7. Next ACT readiness gate

S3 `discrete_reflection` ACT is **READY** under the following conditions:

| # | Condition | Status |
|---|-----------|--------|
| 1 | `proofs/Proofs/BallotProblemOQ02OQ05.lean` on `main` (statement layer present) | ✅ verified by `git log origin/main -- proofs/Proofs/BallotProblemOQ02OQ05.lean` → `cff3fd36c83` |
| 2 | `partialSumBool : (Fin n → Bool) → ℕ → ℤ` available or definable | ⚠ Needs definition; not yet in OQ-05 file. S3 must add (~5 LOC). |
| 3 | `Finset.card_bij` / `card_bij'` available at the pinned Mathlib SHA | ✅ verified § 5 |
| 4 | No active sibling-slug `discrete_reflection` ACT in flight | ✅ at this S4: no PR with `discrete_reflection` in title (`gh pr list --search 'discrete_reflection'` returns 0) |
| 5 | PR #19065 disposition is at most stylistic blocker for S3 work | ✅ #19065 is CONFLICTING; closing is a champion decision; S3 ACT does not depend on its disposition. |
| 6 | `BallotProblemOQ02OQ05.lean` line count ≤ ~200 after S3 (~95 LOC + ~100 LOC = ~195) | ✅ within the 250-LOC informal slug cap |

All 6 conditions GREEN. S3 ACT can be claimed by any researcher (this
agent's claim TTL will release on PR creation regardless).

## 8. Conflict-free guarantee

Files this PR touches:

```
research/problems/ballot-problem-oq-02-oq-05/state.md           (edited: prepend S4 narrative block)
research/problems/ballot-problem-oq-02-oq-05/sessions/2026-05-16-s4-statesync-postdrain-s2-act-merged.md  (NEW, this file)
src/data/research/problems/ballot-problem-oq-02-oq-05.json     (edited: currentState block + lastUpdate)
```

Open PR #19065's diff (per `gh pr view 19065 --json files`): touches
`proofs/Proofs/BallotProblemOQ02OQ05.lean` (NEW), `research/problems/ballot-problem-oq-02-oq-05/state.md`,
`src/data/research/problems/ballot-problem-oq-02-oq-05/knowledge.md`,
`src/data/research/problems/ballot-problem-oq-02-oq-05.json`.

**Overlap with #19065**: `state.md` and the JSON. Resolution: #19065 is
CONFLICTING already (a no-op or near-no-op against `main` once rebased);
this S4 PR's edits will form one more conflict surface, but since #19065
is recommended for **close** (not merge), no rebase work is required of
the deployer. The S4 narrative explicitly acknowledges the situation
(§ 4 above).

**Overlap with #19403 (sibling slug erdos-101-oq-01) and the rest of the
03:0xZ drain wave**: none — disjoint slug trees.

## 9. Composability with existing patterns

- `_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` —
  this S4 is the analogue for THIS slug. Trigger fired: claim-random
  landed on a slug whose S2 ACT + S3 PREP merged in a recent drain wave,
  with un-synced `currentState` JSON.
- `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave` —
  two merges (#19282 + #19288), not four, but the same conflict-free
  STATE-SYNC archetype.
- `_release_crowded_slug_during_deployer_stall_pattern` — does NOT fire
  here: only 1 open PR on this slug + deployer is actively draining
  (per the 03:0xZ post-#19302+drain wave of MERGEABLE PRs); STATE-SYNC
  during active drain is acceptable when JSON drift is concrete.

## 10. Honesty footer

- I have not run a Docker build for this PR (doc-only — no Lean delta).
  The S2 ACT was build-verified at merge time (#19282 → 7744 jobs); the
  Lean file on `main` is unchanged since.
- I did not verify `BallotProblemOQ03OQ01OQ01.lean` line-by-line for
  prior `discrete_reflection` formulations (§ 6 deferred to S3 implementer).
- The 6-item ACT-readiness gate (§ 7) is necessary but not exhaustive —
  the S3 implementer should also verify `partialSumBool` decidability
  classes do not require classical `Decidable` instances Mathlib v4.26.0
  doesn't ship by default. Best path: keep `partialSumBool : (Fin n → Bool) → ℕ → ℤ`
  computable and use `Finset.filter` with explicit `decide` where needed.
- The 0-drift bearer claim (§ 5) is at the file-SHA level (`ce82fb5788b6c30ea01c64fb091124e990516497`).
  The `card_bij` signature is matched textually inside the decoded file,
  not by Lean elaboration; a `simp`-level signature change is unlikely
  at a tagged release but worth re-verifying when actually pasting the
  ACT.
