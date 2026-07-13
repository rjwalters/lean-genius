# S5b PREP — coordination note for pending PR #19001 (S5b ACT parent-file repair, doc-only)

**Date**: 2026-05-15 (~01:20 UTC)
**Researcher**: researcher-43373 (researcher-8 worktree)
**Mode**: coordination PREP (doc-only, no state.md / JSON / Lean edits — all owned by open PR #19001)
**Status**: conflict-free with the eleven prior merged session entries
(S1 OBSERVE #18275 / S2 PREP #18355 / S2c REFINE #18385 / S2d PREP #18656 /
 S3 PREP #18415 / S3a PREP #18469 / S4 PREP #18565 / S4b PREP #18701 /
 S4c PREP #18848 / S5a PREP #18978 / and the open S5b ACT #19001).

## 0. TL;DR

State.md `Phase: PREP, Iter 3, Next Action` (last updated 2026-05-13 by S5a
PREP / researcher-12) reads: *Stage 1 (doctor/mechanic scope) — restore build
of `eTranscendental.lean` and `ETranscendentalOQ03.lean` on origin/main.
Three independent fix points …*

That stage-1 deliverable is **already shipped and awaiting deployer merge**
as PR #19001 — opened 2026-05-14T05:19:31Z by researcher-9 on branch
`research/researcher-9-nth-root-1778735188`. The PR applies four one-line
v4.26.0 fixes (three predicted by S5a §1.1 / §1.2 plus one direction
mismatch that surfaced after Fix #1 unblocked the first-error site), and
its build log shows `Build completed successfully (3071 jobs)`. The PR
is `MERGEABLE` / `CLEAN` but has been in that state for ~19.9 h.

This 19.9 h staleness is consistent with a **system-wide deployer stall**:

- Most-recent merge to `origin/main`: PR #18983 at 2026-05-14T03:05:23Z
  (~22.2 h ago at write-time of this note).
- 100+ currently-open PRs are `MERGEABLE` / `CLEAN` (the
  `gh pr list --state open --limit 100` window saturated at all-100-clean).
- This worktree's local main is at the same SHA as `origin/main` after
  `git fetch`; no merges have landed in the interval.

Per memory `feedback_researcher_deployer_stall_coordination_prep_pattern.md`:
when state.md `Next Action` is already shipped as an open mergeable PR
*and* the system shows a deployer stall (>12 h zero-merge gap + ≥10
stuck mergeable PRs), do **not** redo work or open a conflicting ACT.
Write a short doc-only coordination PREP flagging the open PR + the
post-merge sequencing. This is that note.

Two ~same-day write-ups by the same researcher cover the system-wide
deployer stall in more detail and are cross-referenced here rather than
re-written:

- **PR #19186** (`research(zsqrtd-neg-two-oq-03): S8 PREP — PR coordination
  audit + stranded-branch follow-up + S4 PREP line-erratum (doc-only)`).
  ~223 LOC; primary write-up of the deployer-stall hypothesis with the
  full enumeration of stuck PRs and the proposed escalation cadence.
- **PR #19188** (`research(hilbert-14-oq-04): S3 PREP — coordination note
  for pending PR #18988 (S2-finite ACT, doc-only)`). ~86 LOC; sibling
  coord PREP for `hilbert-14-oq-04` whose ACT PR #18988 sits at the same
  stuck-mergeable stage as this slug's #19001.

This note follows the same scope discipline: **one new file** (this one),
**no edits** to state.md / JSON / meta.json / Lean — those are owned by
the open PR #19001 and the still-open downstream sequence (S5c paste-in
+ S5d optional Mathlib PR).

## 1. PR #19001 audit (S5b ACT, parent-file repair)

### 1.1 Metadata snapshot (2026-05-15 01:15 UTC)

```
number          : 19001
state           : OPEN
title           : research(nth-root-irrational-oq-03): S5b ACT — parent-file repair
                  restores build (4 one-line Mathlib v4.26.0 fixes)
createdAt       : 2026-05-14T05:19:31Z
updatedAt       : 2026-05-14T05:19:31Z (no edits since open)
mergeable       : MERGEABLE
mergeStateStatus: CLEAN
statusCheckRollup: []   (no CI required for doc-light / Docker-verified slugs)
headRefName     : research/researcher-9-nth-root-1778735188
changedFiles    : 5
+/-             : +394 / -13
```

Age at write-time of this note: **~19.9 h since open**, **0 updates** since
open. Comparable freshly-merged research ACT PRs typically merge within
2–4 h of open; the 5x–10x stretch is the deployer-stall signature.

### 1.2 Files changed (verified `gh pr diff --name-only`)

```
proofs/Proofs/ETranscendentalOQ03.lean
proofs/Proofs/eTranscendental.lean
research/problems/nth-root-irrational-oq-03/sessions/2026-05-14-s5b-act-parent-file-repair.md
research/problems/nth-root-irrational-oq-03/state.md
src/data/research/problems/nth-root-irrational-oq-03.json
```

Note that PR #19001 already updates **state.md** and **the JSON** — so this
coord PREP must avoid touching either to stay merge-conflict-free.

### 1.3 What the PR ships (verbatim from its body §"The four fixes")

1. **`eTranscendental.lean`** — add
   `import Mathlib.RingTheory.Localization.Integral`. Resolves 8
   `Unknown constant IsFractionRing.isAlgebraic_iff` errors at lines
   152, 164, 184, 198, 213, 215, 224, 228.
2. **`eTranscendental.lean:225`** — replace `isAlgebraic_algebraMap (1 : ℚ)`
   with `isAlgebraic_one` (v4.26.0 elaborator no longer auto-bridges
   `algebraMap ℚ ℝ 1` to `(1 : ℝ)`).
3. **`ETranscendentalOQ03.lean:118`** — add `import Proofs.eTranscendental`
   and replace `irrational_exp_iff.mpr (by norm_num : (1 : ℚ) ≠ 0)` with
   project-local `e_irrational` (Mathlib `irrational_exp_iff` upstream-removed
   during `Mathlib.Data.Real.Irrational` → `Mathlib.NumberTheory.Real.Irrational`
   refactor; the old import is now a `deprecated_module` alias).
4. **`eTranscendental.lean:152`** — flip `.mp` → `.mpr` (direction outlier
   among the 8 sites of `IsFractionRing.isAlgebraic_iff`; surfaced after
   Fix #1 unblocked Lean's elaboration beyond the first-error site).

Build verified: `Build completed successfully (3071 jobs)` (build log
`.loom/logs/researcher-9-nthroot-s5b-build2.log`).

### 1.4 Cross-slug check

- `IsFractionRing.isAlgebraic_iff` — used **only** in `eTranscendental.lean`
  among `proofs/Proofs/`. No cross-slug breadcrumbs from Fix #1.
- `irrational_exp_iff` — used **only** in `ETranscendentalOQ03.lean` (line
  118) among `proofs/Proofs/`. No cross-slug breadcrumbs from Fix #3.
- `isAlgebraic_algebraMap (1 : ℚ)` (the specific pattern Fix #2 replaces)
  — verified zero hits elsewhere in `proofs/Proofs/`.

Conclusion: PR #19001 is **self-contained** to the two parent files; it
will not unmask new errors elsewhere on merge.

### 1.5 Coverage map vs S5a §1 inventory

| S5a §1 error | Predicted? | Fix in PR #19001 |
|--------------|------------|------------------|
| `ETranscendentalOQ03.lean:118` `Unknown identifier irrational_exp_iff.mpr` | yes (§1.1) | Fix #3 |
| `eTranscendental.lean:151/164/183/198/212/214/224/228` `Unknown constant IsFractionRing.isAlgebraic_iff` | yes (§1.2) | Fix #1 |
| `eTranscendental.lean:225` type-mismatch on `isAlgebraic_algebraMap 1` | yes (§1.2) | Fix #2 |
| `eTranscendental.lean:152` `.mp/.mpr` direction outlier | **no** (post-Fix-#1 secondary) | Fix #4 |

The fourth fix was a true post-elaboration discovery: with the first-error
site cleared (Fix #1 makes `IsFractionRing.isAlgebraic_iff` resolvable),
Lean now type-checks the line-152 application and finds the
direction-of-iff mismatch. S5a PREP could not have predicted this in
advance because Lean stops at first error per file. Researcher-9's S5b ACT
report (`.../sessions/2026-05-14-s5b-act-parent-file-repair.md`) audits
all 8 `IsFractionRing.isAlgebraic_iff` sites to confirm line-152 is the
*unique* direction outlier (the other 7 sites use the same convention
direction as the surrounding context).

## 2. Deployer-stall context

### 2.1 Evidence (2026-05-15 ~01:15 UTC)

- Last merge to `origin/main`: 2026-05-14T03:05:23Z (PR #18983 family of
  same-second merges from the prior deployer cycle). **22.2 h ago.**
- `gh pr list --state open --limit 100 --json mergeable,mergeStateStatus`:
  all 100 returned are `MERGEABLE` / `CLEAN`. The 100-cap saturates; the
  true count of stuck mergeable PRs is ≥ 100.
- Cluster of contemporaneous coord PREPs by this researcher (researcher-8
  worktree, same session, all OPEN):
  - PR #19186 — zsqrtd-neg-two-oq-03 S8 PREP
  - PR #19188 — hilbert-14-oq-04 S3 PREP
  - PR #19189 — zsqrtd-neg-two-oq-03 S4 PREP r2 (post-#19008 line-shift refresh)

  All four (incl. this one when opened) are themselves stuck-mergeable
  on identical grounds, so they cannot help bootstrap merges; they
  document the stall in pieces.

### 2.2 Threshold for escalation

Per memory `feedback_researcher_deployer_stall_coordination_prep_pattern.md`,
the stalled-PR signature is:

- most-recent-merge > 12 h ago — **satisfied** (22.2 h)
- ≥ 10 stuck mergeable PRs of age > 12 h — **satisfied** (≥ 100)
- target PR age > 12 h — **satisfied** (19.9 h)

This crosses every threshold for treating PR #19001 as deployer-stall-
blocked. Per the pattern, **the correct action is to wait + document**,
not to redo work or open a conflicting ACT.

### 2.3 What this PREP does NOT do

- Does **not** edit `state.md` (PR #19001 owns the state.md update from
  Iter 3 → Iter 4 / phase ACT iter+1; my edit here would create a
  three-way merge conflict).
- Does **not** edit `src/data/research/problems/nth-root-irrational-oq-03.json`
  (same reason — PR #19001 owns this).
- Does **not** create a competing parent-file repair PR (researcher-9's
  fixes are correct, Docker-verified, and minimal; redo would waste a
  rebuild cycle and produce a merge conflict with #19001).
- Does **not** start S5c (the proof-body paste-in) — see §3 below for why.

## 3. Post-merge sequencing

Once PR #19001 merges and `origin/main` once again builds the
`Proofs.ETranscendentalOQ03` chain:

### 3.1 S5c (researcher scope, next iteration)

Paste in the ~85-LOC S2 ACT proof body from S5a §3
(`.../sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md`,
§3). Target: `ETranscendentalOQ03.lean` around line 114 (the
`axiom irrational_liouvilleWith_two` line, post-merge line number TBD —
PR #19001 does not delete or move this axiom).

- Sub-targets (from S5a §3): main theorem body + ~50-LOC helper
  `rat_approx_bounded_den_finite` for slice-finiteness.
- Estimated effort: **15–30 min** post-paste-in, including
  `docker-build.sh Proofs.ETranscendentalOQ03` verify cycle.
- Estimated success rate: high — S5a §3 was carefully drafted against
  the pinned Mathlib SHA `2df2f015...` API verified by S4c PREP.
- On success: decrement `axiomCount` 2 → 1 in
  `src/data/proofs/e-transcendental-oq-03/meta.json`, update `state.md`
  phase to ACT iter+1, drop a session note
  (`2026-05-NN-s5c-act-irrational-liouvillewith-two-discharge.md`).

### 3.2 S5d (optional, post-S5c)

Generalize the slice-finiteness helper into a reusable Mathlib-style PR:
`Set.Finite {q : ℚ | q.den ≤ N ∧ |x - q| < 1/q.den^p}` for any `p > 1`
and any real `x`. Mathlib API gap noted in S2c REFINE §3 / PR #18385.

- Scope: upstream Mathlib PR, not project-local. ~60–100 LOC.
- Pre-condition: S5c must land first so the project-local proof of the
  shape exists to reference in the upstream PR description.
- Not gating for any downstream slug; pure value-add.

### 3.3 Independent track: `axiom hermite_lindemann`

Still gated on upstream Mathlib PR #28013 merge. Last `updated_at` known:
2026-05-12T09:28:36Z. At write-time of this note (2026-05-15 01:15 UTC)
that is **~64 h stale** — comfortably past S4c PREP's 24 h re-check
cadence but **not yet** at the 7×24h = 168 h threshold to promote S6
(local re-prove ~700–900 LOC) from "deferred" to "consider scoping".

Cadence check after S5b ACT merges:

```bash
gh pr view 28013 -R leanprover-community/mathlib4 --json headRefOid,updatedAt
```

If still `2026-05-12T09:28:36Z` at the time S5c is started, this gate
remains green and S5c can proceed without dependency on #28013. If
#28013 has moved, S5e (apply S4 PREP §3.4's 5-LOC bridge for
`hermite_lindemann` in `HermiteLindemann.lean`) becomes immediately
schedulable in parallel with S5c.

## 4. Race notes

This PREP creates **exactly one** new file:

```
A research/problems/nth-root-irrational-oq-03/sessions/2026-05-15-s5b-prep-coordination-pr19001-pending.md
```

- 0 Lean files modified.
- 0 edits to `state.md`.
- 0 edits to `src/data/research/problems/nth-root-irrational-oq-03.json`.
- 0 edits to `src/data/proofs/e-transcendental-oq-03/meta.json`.

Pre-push race check (T-15min, 2026-05-15 ~01:15 UTC):

```
$ gh pr list -R rjwalters/lean-genius --search "nth-root-irrational-oq-03 in:title" --state open
  → 1 open: PR #19001 (S5b ACT parent-file repair). This PREP does NOT
            touch any file owned by #19001. Conflict-free.
$ gh pr list -R rjwalters/lean-genius --search "eTranscendental.lean OR ETranscendentalOQ03.lean" --state open
  → only PR #19001. No competing parent-file PRs.
```

The session note + nothing else counts as **1 STATE-SYNC-style PR**
against any 2-per-session cap (per memory
`feedback_researcher_state_sync_active_thread_prep_backlog.md`). No
overlap with the three contemporaneous coord PREPs (#19186, #19188, #19189)
since each touches a distinct slug's `sessions/` directory.

## 5. Self-review checklist

- [x] PR #19001 is verified `MERGEABLE` / `CLEAN` at write-time.
- [x] PR #19001's build log records `3071 jobs clean` per its PR body.
- [x] PR #19001's four fixes cover S5a §1's inventory (1.1 + 1.2) +
      one post-elaboration discovery (line-152 direction outlier).
- [x] `irrational_exp_iff` confirmed absent from Mathlib v4.26.0 (S5a §1.1
      did this work; not re-fetched in this coord PREP).
- [x] `IsFractionRing.isAlgebraic_iff` confirmed at
      `Mathlib/RingTheory/Localization/Integral.lean:139` per PR #19001's
      §1 (not re-fetched in this coord PREP).
- [x] Cross-slug grep for both lemmas: zero hits outside the two parent
      files (S5b ACT session note §"Cross-slug check" did this work).
- [x] System-wide deployer stall confirmed:
      most-recent-merge `2026-05-14T03:05:23Z` is 22.2 h ago and ≥ 100
      mergeable+clean PRs are stuck.
- [x] No state.md / JSON / meta.json / Lean edits in this PR.
- [x] No competing ACT or parent-file repair attempt.

## 6. Memory feedback applicability

This PREP exercises:

- `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
  (primary): triggered by stale-mergeable PR + system-wide stall.
- `feedback_researcher_cross_pr_coordination_audit_pattern.md`: §1.5
  table audits PR #19001 vs S5a §1 inventory.
- `feedback_researcher_state_sync_active_thread_prep_backlog.md`: keeps
  this PREP doc-only and within the 2-per-session cap.

This PREP does **not** exercise (and explicitly avoids):

- `feedback_researcher_stranded_loop_commit_rescue_pattern.md` —
  `git log --all --grep="nth-root-irrational-oq-03"` shows the S5b ACT
  commit `effa2149429` is **on PR #19001's branch**, not stranded. No
  rescue needed.
- `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md` —
  no overlay required; the parent-file repair PR is real and not yet
  applied locally, but this PREP does not build any Lean, so no overlay.
- `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md` —
  the parent-file unblocker is PR #19001; this PREP does not bundle a
  parent fix into a research PR.
