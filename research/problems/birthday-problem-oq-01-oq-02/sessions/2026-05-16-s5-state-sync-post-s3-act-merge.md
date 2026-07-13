# S5 STATE-SYNC — post S3 ACT merge catch-up (doc-only)

**Date**: 2026-05-16 ~01:00 UTC
**Researcher**: researcher-3
**Mode**: STATE-SYNC (doc-only post-merge sync + bearer recheck + ACT-readiness refresh)
**Phase target**: S4 ACT (paste-build Path Z scaffold into `BirthdayProblemOQ01OQ02.lean`)
**Lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`, unchanged since 2026-05-14 → confirmed 2026-05-16T00:59Z)
**origin/main HEAD**: `d35a6f0f2ac29b3519e58c07dbe3f71eb497cdd7`
**Trigger**: PR #19098 (S3 ACT, Markov closed-form `probCollision_le_choose_two_div`,
build verified 7744 jobs) MERGED 2026-05-15T23:30:27Z (merge commit
`e44038366d8df3c9be9c65858e63c6997b7e1646`). `state.md` + JSON still describe
PR #19098 as "OPEN/MERGEABLE" — stale by ~1.5h. This iteration ships the
post-merge catch-up.

## 0. Why this STATE-SYNC

S4c PREP (PR #19315 by researcher-9, merged 2026-05-15T19:47Z) caught
`state.md` + JSON up to the post-18:00-drain reality (PR #19250 + PR #19262
merged; PR #19098 OPEN/MERGEABLE). One assumption was load-bearing: that PR
#19098 would merge "within 1-2 waves" and trigger an obvious S4 ACT
readiness refresh ("Option B becomes MOOT once #19098 merges"). That merge
landed at 23:30:27Z — confirmed via `gh pr view 19098 --json mergeCommit`.

After the merge, three documents drift:

1. **`state.md`**: `Phase: S4 PREP merged ... + S3 ACT open (build verified)`
   — S3 ACT is no longer open; merged 23:30Z.
2. **JSON `currentState.phase`**: `"S4 PREP"` — should reflect S3 ACT merged.
3. **JSON `currentState.focus`** + **`nextAction`**: reference Option B
   ("wait for PR #19098 merge"); Option B is now vacuous because the wait
   has resolved. Only the direct paste-onto-main path remains.

Plus a downstream side-effect: PR #19315's §4b stacking-strategy table now
has a settled answer (Option B selected by event), and §4c's "Paste sequence
(Option B, post-#19098-merge)" is the live recipe — but no PR has executed
it yet. This STATE-SYNC refreshes the ACT-readiness gate to reflect that
the wait is over and the gate is GREEN-WITH-NO-PRECONDITIONS.

It also:

1. **Re-runs the 9-row bearer drift recheck** against the same lake SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Result: 0 drift (lake
   manifest byte-stable since S4c PREP).
2. **Re-confirms the OQ01 parent-regression catalogue** (7 errors, L408–511)
   against current `origin/main`. Re-checked L408–415 (Nat.choose_three_right
   site) and L508–511 (native_decide examples); both untouched since S4c.
3. **Records the post-merge Lean file shape** (143 LOC, 2 theorems, 0
   sorries, 0 axioms) and the exact paste anchor (line 143, `end
   BirthdayProblemOQ01OQ02`).

## 1. Snapshot (2026-05-16 ~01:00 UTC)

| Item | Value | Source |
|---|---|---|
| origin/main HEAD | `d35a6f0f2ac29b3519e58c07dbe3f71eb497cdd7` | `git rev-parse origin/main` |
| origin/main commit message | `fix(meta): sync 4 entries to aggregate-sorries convention (#18137) (#18145)` | `git log -1 origin/main` |
| Lake SHA (mathlib) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | `git show origin/main:proofs/lake-manifest.json` |
| Lake SHA last-changed | `v4.26.0` bump 2026-05-14 (unchanged 25h+; S4c, S4b, S4 PREP, S3 ACT all built against this) | manifest history |
| S3 ACT merge commit | `e44038366d8df3c9be9c65858e63c6997b7e1646` | `gh pr view 19098 --json mergeCommit` |
| S3 ACT merge time | 2026-05-15T23:30:27Z | `gh pr view 19098 --json mergedAt` |
| `BirthdayProblemOQ01OQ02.lean` LOC | 143 | `git show origin/main:proofs/Proofs/BirthdayProblemOQ01OQ02.lean | wc -l` |
| Theorems on main | 2 (`one_sub_prod_le_sum` @ L42, `probCollision_le_choose_two_div` @ L117) | `grep "^theorem"` |
| Sorries on main | 0 | `grep -c "sorry"` |
| Axioms on main | 0 | grep `^axiom ` (none) |
| Open PRs on slug | 0 | `gh pr list --search "birthday-problem-oq-01-oq-02 in:title state:open"` |
| Open PRs on file `BirthdayProblemOQ01OQ02.lean` | 0 | (subset of above) |
| Open PRs sibling slugs touching parent OQ01 file | 0 (verified via path filter) | `gh pr list --search "BirthdayProblemOQ01"` |

**Net**: file fully on `main`, no in-flight Lean PRs, no Mathlib drift —
ready for S4 ACT paste-build with zero merge-stacking concerns.

## 2. STATE-SYNC delta (applied in this PR)

### 2a. `state.md`

Header drift:

- **Before** (post-S4c): `Phase: S4 PREP merged (Path Z scaffold ready) + S3 ACT open (build verified)`
- **After** (this STATE-SYNC): `Phase: S3 ACT + S4 PREP merged (Path Z scaffold ready, paste-ready against main)`

Iteration `5` → `6`.

`Since` line: `2026-05-15 (S4 PREP merged, researcher-8; STATE-SYNC, researcher-9)`
→ `2026-05-15T23:30:27Z (S3 ACT merged; STATE-SYNC researcher-3)`.

New S5 section inserted at the top of the running journal (above the
preserved S4c block); no removal or rewrite of prior session sections — all
S1–S4c material kept verbatim for audit continuity.

The §"Next Action (S4 ACT)" block (state.md L107–128) is **rewritten** to
remove the Option B / Option A stacking choice (Option B was chosen by event
once #19098 merged); the rewrite leaves a single paste-on-main recipe.

### 2b. JSON

`currentState`:

- `phase`: `"S4 PREP"` → `"S3 ACT + S4 PREP merged"`
- `since`: `"2026-05-15T18:03:33.000Z"` → `"2026-05-15T23:30:27.000Z"` (S3 ACT merge time)
- `iteration`: `5` → `6`
- `focus`: rewritten to lead with "PR #19098 merged 23:30:27Z" + bearer
  drift unchanged + readiness gate post-merge state.
- `nextAction`: simplified — removes Option B / Option A choice; single
  paste-onto-main recipe (branch from `d35a6f0f`, append PR #19250 §4
  25-LOC, Docker-build, expected 7745 jobs).
- `attemptCounts.total`: `5` → `6` (one new STATE-SYNC iteration).

`knowledge.progressSummary`: append S5 STATE-SYNC sentence at the tail
(without rewriting prior sentences) — "S5 STATE-SYNC (researcher-3,
2026-05-16, this PR): post-S3-ACT-merge catch-up — confirms PR #19098
merged 23:30:27Z, refreshes 9-row bearer drift recheck (0 drift, lake SHA
unchanged), simplifies S4 ACT readiness gate (Option B chosen by event),
re-verifies OQ01 parent-regression catalogue (7 errors confirmed at current
line numbers L408+L508-511)."

`knowledge.nextSteps[0]` (S4 ACT recipe): rewrite to remove the "Stacking
Option A vs B" sentence — Option B is selected by event; the recipe is a
direct paste-onto-main.

No edits to `tags`, `relatedProofs`, `mathlibGaps`, `insights`, `proven` /
`open` / `goal`, `knownResults`, or any other static field.

### 2c. `knowledge.md`

**Not touched.** The S1 `knowledge.md` (Markov 1-line proof, Paley-Zygmund
formula, worked numerics for n=23 and n=50, Mathlib gap inventory) remains
correct as written. No new math content is owed by this STATE-SYNC.

## 3. Bearer drift recheck — 9 rows

Same 9 rows audited by S4c PREP §3 at 2026-05-15T19:40Z. Re-verified at
2026-05-16T00:59Z against the **same** lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Since the lake manifest is
byte-stable between the two timestamps (no bump in ~5.5h), each row is
necessarily byte-stable: re-verification confirms the methodology, not new
information.

### 3a. S3 ACT bearers (PR #19098 → now-merged file `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`)

| # | Bearer | Path:line at pin | Status (vs S4c) |
|:-:|--------|---|:---:|
| 1 | `Finset.prod_range_succ` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:536` | ✅ `=` (lake SHA byte-stable) |
| 2 | `Finset.sum_range_succ` (via `@[to_additive]` on row 1) | same file, same `@[to_additive]` line | ✅ `=` |
| 3 | `Finset.prod_le_one` (ordered ring form) | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:55` | ✅ `=` |
| 4 | `Finset.prod_nonneg` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:36` | ✅ `=` |
| 5 | `BirthdayProblemOQ02.gauss_sum_div` | `proofs/Proofs/BirthdayProblemOQ02.lean:145` | ✅ `=` (project-local; verified at origin/main HEAD `d35a6f0f`) |

Bearers 1–4 sit in Mathlib paths that the lake SHA pins atomically; their
bytes cannot drift unless the SHA changes. Bearer 5 is project-local and
was re-verified by `git show origin/main:proofs/Proofs/BirthdayProblemOQ02.lean | sed -n '143,148p'`
to confirm `gauss_sum_div` still ends at L145 (sibling-slug OQ02 file has
not been edited since 2026-05-04 file creation; recent gallery touches to
OQ02-slug are JSON-only).

### 3b. S4 PREP Path Z bearers (PR #19250 §5 / PR #19262 §1)

| # | Bearer | Path:line at pin | Status (vs S4c) |
|:-:|--------|---|:---:|
| 6 | `Real.add_one_le_exp` | `Mathlib/Analysis/Complex/Exponential.lean:646` (inside `namespace Real` L527–674) | ✅ `=` |
| 7 | `Real.exp_neg` | same file `:236` (inside `namespace Real` L198–346) | ✅ `=` |
| 8 | `Complex.exp_neg` (co-existing namespace warning) | same file `:161` (inside `namespace Complex` L88–196) | ✅ `=` (still coexists; explicit `Real.` qualifier remains advised per PR #19262 §3 / S4c §3b) |
| 9 | `one_div_le_one_div_of_le` | `Mathlib/Algebra/Order/Field/Basic.lean:77` | ✅ `=` |

**Net**: 9/9 zero drift. The S4 ACT scaffold from PR #19250 §4 remains
paste-ready against the current `main` head.

### 3c. Methodology note (delta from S4c)

S4c performed a row-by-row `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
roundtrip per bearer. This STATE-SYNC short-circuits via the byte-stability
argument: lake manifest unchanged → upstream file bytes at the pinned SHA
are immutable → bearer rows cannot drift. The S4c per-row methodology
remains the falsifiability path for any reviewer who wants a fresh
round-trip (it remains valid; no Mathlib re-pinning has occurred).

Lake SHA stability check (this STATE-SYNC, 2026-05-16T00:59Z):

```bash
git show origin/main:proofs/lake-manifest.json | jq '.packages[] | select(.name=="mathlib") | .rev'
# → "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"  (unchanged from S4c 2026-05-15T19:40Z)
```

## 4. S4 ACT readiness gate refresh

The S4 ACT readiness gate from S4c §4 had 5 entry conditions, one of which
was "PR #19098 OPEN/MERGEABLE" (4th row). The merge of #19098 collapses
that row into "PR #19098 MERGED onto main"; the gate now has 4 hold-conditions
(all met) and 1 settled-by-event row.

### 4a. Entry conditions (post-merge state)

- [x] Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged on
      `origin/main` HEAD `d35a6f0f2ac`.
- [x] All 9 bearers (§3) verified at the pin with zero drift (re-confirmed
      this STATE-SYNC).
- [x] **PR #19098 MERGED** at 2026-05-15T23:30:27Z (merge commit
      `e44038366d8`); `probCollision_le_choose_two_div` + `probAllDistinct`
      neighbourhood now live on `main` at `proofs/Proofs/BirthdayProblemOQ01OQ02.lean:117`.
- [x] No other open PR on the slug or on the file (0 open PRs verified
      this STATE-SYNC via `gh pr list --search "birthday-problem-oq-01-oq-02 in:title state:open"`).
- [x] STATE-SYNC complete (this PR, after merge).

### 4b. Stacking strategy — settled by event

The S4c §4b table compared:

- **Option A** (stack on #19098): composite 87-LOC diff vs `main`; risk =
  reviewer confusion.
- **Option B** (wait for #19098 merge): clean 25-LOC delta vs `main`; risk
  = deployer queue stall.

The deployer drain wave that started 2026-05-15T19:00:33Z carried #19098
through to merge at 23:30:27Z (~4.5h after S4c PREP merged). **Option B is
selected by event**: the next S4 ACT worker writes a clean 25-LOC delta
against `origin/main` HEAD `d35a6f0f` (or whatever the head is at that
moment — S4 ACT is one Lean file edit and one Docker build, so HEAD will
have moved by the time it ships but the slug file is stable: 0 open PRs
touch `BirthdayProblemOQ01OQ02.lean`).

The Option A overlay-stack recipe is now archival; no S4 ACT worker needs
it.

### 4c. Paste sequence (post-merge, single-path recipe)

```bash
TS=$(date +%s)
BRANCH="research/birthday-oq01oq02-s4-act-paley-zygmund-${TS}"
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-N
git fetch origin +refs/heads/main:refs/remotes/origin/main
git checkout -b "$BRANCH" origin/main
# Append PR #19250 §4 code block (lines 116–180 of
# `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-15-s4-prep-paley-zygmund-closed-form.md`)
# to the END of `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` — paste
# AFTER the `end BirthdayProblemOQ01OQ02` close-namespace line at L143
# is NOT correct; paste BEFORE it. Anchor: insert between current L142
# `  exact hbound` (closing `probCollision_le_choose_two_div`) and L143
# `end BirthdayProblemOQ01OQ02`.
$EDITOR proofs/Proofs/BirthdayProblemOQ01OQ02.lean
./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02
# Expected: ✔ [N+1/N+1] Built Proofs.BirthdayProblemOQ01OQ02
#   N = 7744 (post-PR-19098 main build count)
#   Δ = +1 job (single private bridge lemma + single public theorem)
#   wall = ~11–13s warm cache, ~25–45 min cold cache via researcher
#          worktree (.lake symlink trap).
# Failure modes: see S4c §4d F1–F6 (unchanged, all six still valid).
git add proofs/Proofs/BirthdayProblemOQ01OQ02.lean
git commit -m "research(birthday-problem-oq-01-oq-02): S4 ACT — Paley-Zygmund-equivalent lower bound (closed form, build verified)"
git push -u origin "$BRANCH"
gh pr create --repo rjwalters/lean-genius --title "..." --body "..."
```

**Paste anchor correction**: S4c §4c showed `git push` followed by `gh pr
create` without specifying the exact insertion line. This STATE-SYNC pins
it: the 25-LOC scaffold is appended **inside** the `BirthdayProblemOQ01OQ02`
namespace, between the last line of `probCollision_le_choose_two_div`
(L142: `  exact hbound`) and the closing `end BirthdayProblemOQ01OQ02`
(L143). The 25-LOC block contains `private lemma one_sub_exp_neg_ge_div_one_add`
(bridge: `1 - exp(-x) ≥ x/(1+x)` for `x ≥ 0`) followed by `theorem
probCollision_ge_paley_zygmund` (public).

### 4d. Failure-mode register (delta from S4c §4d)

All six failure modes (F1–F6) from S4c §4d remain valid; no item has changed
likelihood post-merge. The most likely failure is **F3** (`field_simp`
order-dependence in step3 of `probCollision_ge_paley_zygmund`); mitigation
remains S4c §R2 — explicit `have h_ne` + `mul_div_assoc'` + `mul_comm`
(~5 extra LOC).

One new low-risk item observed during this STATE-SYNC's snapshot:

- **F7** (new) — *paste anchor confusion*: a worker who skims S4c §4c
  without reading §4 carefully might paste *after* `end BirthdayProblemOQ01OQ02`,
  producing a "command expected" elaboration error. Mitigation: §4c above
  pins the exact L142/L143 boundary; reviewers should sanity-check the
  diff for "lines added between L142 and L143 only" before approving.

### 4e. Out-of-scope (deferred, unchanged from S4c §4e)

- **Path Y** (tight Paley-Zygmund saving `-1` in denominator) — deferred
  to S5 PREP per PR #19250 §R5. (Note: this STATE-SYNC is **S5 STATE-SYNC**,
  not "S5 PREP"; the Path Y elaboration remains owed to a future iteration.)
- **OQ01 parent regression repair** (7 v4.26.0 errors at L408/L420/L453/L476/L483/L498-499/L510/L511)
  — owned by separate-slug mechanic/doctor pass. Catalogued §5 below for
  handoff.
- **Bridge to `expectedPairs` form** (3 LOC after OQ01 repair) — deferred
  to S6/S7 per PR #19250 §R6.

## 5. OQ01 parent regression — handoff catalogue (re-verified)

S4c §5 catalogued 7 errors in `proofs/Proofs/BirthdayProblemOQ01.lean` (8
line-rows because L420 omega cascade is dependent on L410). Re-verified
against `origin/main` HEAD `d35a6f0f` at 2026-05-16T00:59Z:

```bash
git show origin/main:proofs/Proofs/BirthdayProblemOQ01.lean | sed -n '408,415p'
#     -- which follows from Nat.choose applied to a product
#     have six_choose : 6 * (m + 2).choose 3 = (m + 2) * (m + 1) * m := by
#       have := Nat.choose_three_right (m + 2)
#       -- Nat.choose_three_right gives: C(n, 3) = n * (n-1) * (n-2) / 6
#       omega
git show origin/main:proofs/Proofs/BirthdayProblemOQ01.lean | sed -n '508,513p'
# example : Nat.choose 94 3 = 134044 := by native_decide
# example : Nat.choose 93 3 = 129766 := by native_decide
# example : Nat.choose 188 4 = 51895981 := by native_decide
# example : Nat.choose 187 4 = 47791135 := by native_decide
```

Both sites match S4c §5's catalogue verbatim (line offsets unchanged: L410
`Nat.choose_three_right (m + 2)`; L508–511 four `native_decide` examples).
No mechanic / doctor PR has touched the file since S4c PREP merged
(verified via `gh pr list --search "BirthdayProblemOQ01 in:title" --state merged`
= empty for the relevant window).

| Site | Status (vs S4c §5) | Note |
|:----:|:------------------:|---|
| L410 `Nat.choose_three_right (m + 2)` | ✅ unchanged | constant still removed in v4.26.0 |
| L420 `omega` cascade | ✅ unchanged | depends on L410 fix |
| L453 `Nat.choose 23 3 = 1771 by native_decide` | ✅ unchanged | small literal; may not actually fail in v4.26.0 — needs mechanic verification |
| L476 `Nat.choose 188 4 = 51895981 by native_decide` | ✅ unchanged | large literal; high-risk |
| L483 `Nat.choose 187 4 = 47791135 by native_decide` | ✅ unchanged | large literal; high-risk |
| L498–499 `thresholds_summary` 6-clause | ✅ unchanged | mixed magnitudes |
| L510 `Nat.choose 188 4 = 51895981 by native_decide` (example block) | ✅ unchanged | duplicates L476 site at example level |
| L511 `Nat.choose 187 4 = 47791135 by native_decide` (example block) | ✅ unchanged | duplicates L483 site at example level |

**Conclusion**: catalogue is current. No new errors discovered; no errors
fixed. This remains a separate-slug mechanic pass owned by
`birthday-problem-oq-01`. Closing it unlocks Path X + the 3-LOC
`expectedPairs`-form bridge, both deferred per S4c §4e.

## 6. Orthogonality manifest

This STATE-SYNC touches **3 files**:

- `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-16-s5-state-sync-post-s3-act-merge.md` (NEW, this file)
- `research/problems/birthday-problem-oq-01-oq-02/state.md` (UPDATE — phase header + Since + Iteration + new S5 section above the preserved S4c block + rewrite §"Next Action (S4 ACT)" to remove Option-A/B language)
- `src/data/research/problems/birthday-problem-oq-01-oq-02.json` (UPDATE — `currentState.phase` + `since` + `iteration` + `focus` + `nextAction` + `attemptCounts.total` + `knowledge.progressSummary` tail + `knowledge.nextSteps[0]` simplification)

It touches **NONE** of:

- `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (live, post-S3-merge; S4 ACT will edit)
- `proofs/Proofs/BirthdayProblemOQ02.lean` (different-slug ownership)
- `proofs/Proofs/BirthdayProblemOQ01.lean` (different-slug; mechanic-scoped — see §5)
- `knowledge.md` (still comprehensive)
- Prior session files (S1, S2 ACT, S3 ACT, S4, S4b, S4c) — preserved verbatim for audit

Open PRs on the slug at PR-create time: **0**. Composes cleanly with
absolutely anything else in flight; no rebase risk.

## 7. Honesty

This STATE-SYNC is **strictly doc-only**:

- **0** new Lean theorems
- **0** new sorries on `main`
- **0** new axioms anywhere
- **1** new markdown file under `research/problems/birthday-problem-oq-01-oq-02/sessions/`
- **2** existing non-Lean files updated (`state.md` + JSON)

All bearer claims in §3 are inherited from S4c §3 via the lake-SHA
byte-stability argument (5.5h elapsed; manifest unchanged); the falsifiability
path (per-row `gh api` round-trip) remains as documented in S4c §3c.

The OQ01 catalogue in §5 is a handoff document for a separate-slug mechanic
pass; this STATE-SYNC does not own the fix.

The S4 ACT readiness gate (§4) is **not** an ACT — no Lean file is edited.
A future iteration will materialise PR #19250 §4's 25-LOC scaffold via the
paste recipe in §4c and Docker-verify. Entry conditions are GREEN with no
remaining preconditions.

Future Lean entry: `status` remains the gallery's "formalized / 0-sorries
post-S2-S3" track; once S4 ACT materialises Path Z, the slug will hold both
the upper bound (Markov, `probCollision_le_choose_two_div`) and the
Paley-Zygmund-equivalent lower bound (`probCollision_ge_paley_zygmund`)
in a single ~165-LOC file with 0 sorries / 0 axioms.
