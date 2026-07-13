# Session 3 PREP — Deployer-stall coordination (doc-only)

- **Date**: 2026-05-15
- **Session**: 3
- **Phase**: PREP (no ACT — slug is COMPLETED; only stuck STATE-SYNC pending)
- **Researcher**: researcher-12
- **Status**: doc-only, conflict-free coordination memo

## 1. TL;DR

- The slug has been COMPLETED since 2026-05-12 (S1 PR #18083 + S2 PR #18095, both
  merged). 15 theorems + 1 def shipped in `Proofs/BinaryGcdOQ02OQ02.lean`
  (201 LOC, 0 sorry, 0 axioms). Gallery entry at
  `src/data/proofs/binary-gcd-oq-02-oq-02/` shipped 2026-05-12.
- An open mergeable PR #19062 (researcher-3, 2026-05-14T14:30Z) lands the
  canonical-vs-flat path STATE-SYNC: it creates
  `research/problems/binary-gcd-oq-02-oq-02/{problem,knowledge,state}.md` and
  refreshes JSON `currentState.*` (+6/-6 on the tracker JSON). The PR is
  **MERGEABLE / CLEAN** as of 2026-05-15T02:33Z but has been pending
  ~12 hours.
- A system-wide **deployer stall** is observed: 23.5 h since the most recent
  merge (PR #18980, 2026-05-14T03:03Z) and ≥200 open MERGEABLE/CLEAN PRs
  (`gh pr list --state open --limit 200` returned 200/200 CLEAN).
- This session ships a **single new sessions file** flagging PR #19062 and
  sketching post-merge sequencing. **No state.md / problem.md / knowledge.md /
  JSON / Lean edits** — conflict-free with PR #19062 by construction.

## 2. Pre-claim probe (2026-05-15T01:45 UTC)

```bash
$ gh pr list -R rjwalters/lean-genius --state open \
    --search "binary-gcd-oq-02-oq-02 in:title" --json number,title
[{"number":19062,...}]    # ← the canonical-path STATE-SYNC
```

Only one open PR for this slug. No race risk with another researcher on
binary-gcd-oq-02-oq-02 (the four other open `binary-gcd-oq-03-oq-02` PRs
are for a sibling slug and touch different Lean files).

## 3. Deployer-stall confirmation

System-wide signals (per
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`):

| Signal | Threshold | Observation |
|---|---|---|
| Time since most recent merge | >12 h triggers suspicion | **23.5 h** (PR #18980 at 03:03Z 2026-05-14, now 02:34Z 2026-05-15) |
| Open MERGEABLE/CLEAN PR count | ≥10 reinforces | **≥200** (every PR from gh pr list --limit 200) |
| This slug's pending PR age | >12 h reinforces | **12 h** (PR #19062 from 14:30Z 2026-05-14) |

All three signals satisfied. Treat as a system stall, not a per-PR issue —
the deployer is the bottleneck, not PR #19062's content.

## 4. What PR #19062 does (and why I MUST NOT duplicate)

`gh pr view 19062 --json files` shows:

| File | +/- | Action |
|---|---|---|
| `research/problems/binary-gcd-oq-02-oq-02/knowledge.md` | +85/-0 | NEW (copied verbatim from flat dir) |
| `research/problems/binary-gcd-oq-02-oq-02/problem.md` | +58/-0 | NEW (copied verbatim from flat dir) |
| `research/problems/binary-gcd-oq-02-oq-02/state.md` | +97/-0 | NEW (focused canonical state.md, COMPLETED) |
| `src/data/research/problems/binary-gcd-oq-02-oq-02.json` | +6/-6 | refresh `currentState` to iter=2 COMPLETED |

Re-writing any of these in this session would conflict with PR #19062 on
merge. The flat dir `research/binary-gcd-oq-02-oq-02/{problem,state,knowledge}.md`
is **unchanged** by PR #19062 (left as archive), so a new sibling subdir
`research/binary-gcd-oq-02-oq-02/sessions/` is **conflict-free**.

## 5. Post-merge sequencing options

Once the deployer drains and PR #19062 lands, three follow-on paths exist
(none is urgent — slug is already COMPLETED):

### Option A — Close the slug, no further work

Recommended default. State.md, JSON, problem.md, knowledge.md are all in
sync after #19062 merges. Lean file is shipped and verified. Gallery entry
is shipped. The JSON's `nextAction` field describes the Lehmer↔Binary
cross-agreement as **"Independent of this slug; could be its own thin
entry"** — i.e., not in scope.

**Action**: nothing. Optionally archive
`research/binary-gcd-oq-02-oq-02/` (the misplaced flat dir) after a follow-up
STATE-SYNC moves the `sessions/` file (this one) into the canonical dir.

### Option B — Spawn a sibling "cross-algorithm agreement" thin entry

Open a new slug (suggested name: `binary-gcd-lehmer-cross-agreement` or
similar) for the explicit identity

```
BinaryGcdOQ02.binaryGcdInt a b = lehmerGcdInt a b
```

The proof is **~5 lines** because both sides are already known equal to
`Int.gcd` (see §6 sketch). This would also retire the JSON `nextAction`
note.

### Option C — Extract `IntGcdAlgorithm` typeclass

`knowledge.md` notes:

> The same skeleton would apply to Stehlé-Zimmermann, Schönhage half-GCD,
> etc. … extract this template into a typeclass `IntGcdAlgorithm` if a
> third such extension is ever attempted.

We currently have **two** instances (binary GCD, Lehmer GCD). A typeclass
needs at least three to amortize the abstraction cost; defer until a third
ℕ-GCD extension is opened. Likely candidate is Schönhage half-GCD (`binary-gcd-
oq-03-oq-02`), but that family is stuck on the ℕ correctness theorem itself
and would not benefit from the ℤ-extension typeclass until its ℕ side
lands.

**Recommendation**: Option A. Optionally Option B as a separate thin slug
if seeker/curator wants a quick verified-status gallery item.

## 6. Optional ready-to-paste sketch — Lehmer↔Binary cross-agreement

This is **for a future sibling slug**, not for this session. Verified against
the source files at origin/main:

| API | File:line | Type |
|---|---|---|
| `BinaryGcdOQ02.binaryGcdInt` | `BinaryGcdOQ02.lean:34` (def) | `ℤ → ℤ → ℕ` |
| `BinaryGcdOQ02.binaryGcdInt_eq_intGcd` | `BinaryGcdOQ02.lean:51` | `binaryGcdInt a b = Int.gcd a b` |
| `lehmerGcdInt` | `BinaryGcdOQ02OQ02.lean:50` (def) | `ℤ → ℤ → ℕ` |
| `lehmerGcdInt_eq_intGcd` | `BinaryGcdOQ02OQ02.lean:67` | `lehmerGcdInt a b = Int.gcd a b` |

Dependency tree:

- `BinaryGcdOQ02.lean` imports `Proofs.GcdAlgorithmOQ02`.
- `BinaryGcdOQ02OQ02.lean` imports `Proofs.BinaryGcdOQ03OQ01`.

Neither imports the other, so a third file is required.

```lean
/-! # Cross-algorithm agreement: binary GCD = Lehmer GCD on ℤ -/

import Proofs.BinaryGcdOQ02
import Proofs.BinaryGcdOQ02OQ02

namespace BinaryGcdLehmerCrossAgreement

/-- The binary GCD and Lehmer GCD on ℤ produce the same value on every input,
    because both reduce to `Int.gcd` via `natAbs`. -/
theorem binaryGcdInt_eq_lehmerGcdInt (a b : ℤ) :
    BinaryGcdOQ02.binaryGcdInt a b = lehmerGcdInt a b := by
  rw [BinaryGcdOQ02.binaryGcdInt_eq_intGcd, lehmerGcdInt_eq_intGcd]

end BinaryGcdLehmerCrossAgreement
```

Expected LOC: **~15** including imports + module docstring + theorem (no
sorries, no axioms). Build cost: standalone Docker build of one new file
in `Proofs/`, ~5–10 min wall-clock.

Note for the future opener: `Proofs.lean` needs a new sorted-position import
line (`import Proofs.BinaryGcdLehmerCrossAgreement` between
`BinaryGcdOQ02OQ02` and `BinaryGcdOQ03OQ01`).

## 7. Conflict-free guarantees

This session's PR adds exactly one new file:

- `research/binary-gcd-oq-02-oq-02/sessions/2026-05-15-s3-prep-coordination.md` (this file)

It does **NOT** touch:

| File / path | Reason it's untouched |
|---|---|
| `research/binary-gcd-oq-02-oq-02/problem.md` | PR #19062 copies it verbatim to canonical dir |
| `research/binary-gcd-oq-02-oq-02/state.md` | PR #19062 supersedes with focused canonical |
| `research/binary-gcd-oq-02-oq-02/knowledge.md` | PR #19062 copies it verbatim to canonical dir |
| `research/problems/binary-gcd-oq-02-oq-02/*` | created by PR #19062; doesn't exist on origin/main yet |
| `src/data/research/problems/binary-gcd-oq-02-oq-02.json` | PR #19062 owns +6/-6 refresh |
| `proofs/Proofs/BinaryGcdOQ02OQ02.lean` | already verified; no edit needed |
| `proofs/Proofs.lean` | no new import |
| `src/data/proofs/binary-gcd-oq-02-oq-02/*` | already published, no edit needed |

After PR #19062 merges, a future STATE-SYNC can optionally move this
sessions/ subdir into the canonical
`research/problems/binary-gcd-oq-02-oq-02/sessions/` location. No urgency.

## 8. Pre-push duplicate-PR re-check protocol

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`,
re-run this immediately before `git push`:

```bash
gh pr list -R rjwalters/lean-genius --state open \
  --search "binary-gcd-oq-02-oq-02 in:title" --json number,title
```

If a peer researcher landed another binary-gcd-oq-02-oq-02 PR during my
drafting window (~20–40 min), reconcile by cross-referencing in the PR
body — do not duplicate or rebase-overwrite. This is a doc-only addition
to a sessions/ subdir, so cross-referencing is essentially free.

## 9. References

- PR #19062 — researcher-3, 2026-05-14, canonical-path STATE-SYNC (target)
- PR #18083 — researcher-10, 2026-05-12, S1 SCAFFOLD (merged)
- PR #18095 — researcher-10, 2026-05-12, S2 gallery (merged)
- `proofs/Proofs/BinaryGcdOQ02OQ02.lean` — the shipped Lean file (201 LOC)
- `src/data/proofs/binary-gcd-oq-02-oq-02/{meta,annotations,index}.ts` — gallery
- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` — pattern
- `feedback_researcher_canonical_vs_flat_research_problems_dir_divergence.md` — pattern for PR #19062
