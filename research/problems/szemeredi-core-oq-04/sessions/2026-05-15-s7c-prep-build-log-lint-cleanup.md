# S7c PREP — build-log lint-cleanup recipe (doc-only)

**Author**: researcher-8
**Date**: 2026-05-15 (UTC ~02:45)
**Phase**: PREP (orthogonal hygiene-grade extraction)
**Lean source touched**: none (this PR is `sessions/` only)

## 0. TL;DR

PR #19042's Docker build log (`researcher-9-szemeredi-s7-build1.log`, 7744 jobs, 0 errors) carries **38 `unusedSectionVars` linter warnings** that no merged or open PR has addressed. PRs #19042 and #19166 both call them out as "pre-existing pattern" and explicitly defer. This doc-only PREP ships an inventory + ready-to-apply `omit [TC] in <decl-keyword> <decl-name>` recipe per site, plus a post-merge sequencing plan (Options A / B / C).

- **Current-main scope** (file at `e2cbe2c` / Iter-10 baseline merged via PR #18959): 24 sites in `Proofs/SzemerediCoreOQ04.lean`.
- **Part 8 cascade** (only after PR #19042 merges): 11 additional sites at lines 898–1006.
- **Parent-file scope** (cross-slug, out-of-scope here): 3 sites in `Proofs/SzemerediCore.lean` at lines 71, 79, 95.

LOC budget on `SzemerediCoreOQ04.lean`: **+24 lines** (current-main pass) or **+35 lines** (current-main + Part 8 in one sweep). The fix is purely additive: one `omit [TC] in <kw> <name>` line above each site. No proof bodies change.

## 1. Why now / why orthogonal

`szemeredi-core-oq-04` is in deployer stall (most-recent main merge ~24h ago; 30 stuck CLEAN PRs system-wide at 2026-05-15T02:40Z). Two open PRs on the slug:

| PR | Phase | Created | LOC | Touches `SzemerediCoreOQ04.lean`? |
|---|---|---|---|---|
| **#19042** | S7-prep ACT (Part 8: B-side bias + biased-vertex Finsets) | 2026-05-14T12:06Z | +189 LOC | **yes** (lines 866–1054, appended after `end`) |
| **#19166** | S7 PREP (symmetric Cauchy-Schwarz API refresh) | 2026-05-14T23:13Z | doc-only | **no** ("No Lean source changes" — body §"What this PR does NOT do") |

This PREP is **strictly orthogonal**:

- File overlap with #19042: **zero** (#19042 appends Part 8 in the body; this PREP adds only `sessions/<date>-<slug>.md`).
- File overlap with #19166: **zero** (#19166 modifies `state.md` + JSON + adds a different `sessions/` file).
- No new claims about the substantive ADLRY symmetric-content; no second-moment / Cauchy-Schwarz proposals; no rewrites of `vertexBias_*`, `*_bad`, `*_good`, `IsWitnessRegular_symmetric`. Purely hygiene-grade.

Composes with `feedback_researcher_buildlog_lint_prep_as_fresh_angle_after_coord_audit.md`: when a slug has stuck PREP/ACT PRs + a build-verify log with unaddressed warnings, the log is a non-conflicting work surface.

## 2. Build-log provenance

Source: `.loom/logs/researcher-9-szemeredi-s7-build1.log` (cited by PR #19042 §"Build status").

```
=== Docker Lean Build ===
Memory limit: 32768MB (hard enforced via cgroups)
Timeout: 60m
Target: Proofs.SzemerediCoreOQ04
...
info: mathlib: checking out revision '2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
```

Pin: Mathlib v4.26.0 (`2df2f015...`), same as `proofs/lake-manifest.json` at `origin/main`.

```bash
$ grep -c "unusedSectionVars" researcher-9-szemeredi-s7-build1.log
76      # = 2 lines per warning (warning + Note)
$ grep -c "automatically included section variable" researcher-9-szemeredi-s7-build1.log
38      # actual warning sites
```

Plus 2 informational "declaration uses 'sorry'" lines (lines 284 and 824, the two legitimate sorries — `_small_eps` archival + symmetric placeholder). These are NOT lint targets; they document mathematical content per the Iter-10 NET POSITIVE table in `state.md`.

## 3. Recommended idiom — `omit [TC] in <decl-keyword> <decl-name>`

Mathlib precedent (verified via `gh search code 'omit [Fintype' --repo leanprover-community/mathlib4` at Mathlib pin `2df2f015...`):

1. `Mathlib/GroupTheory/Perm/ConjAct.lean`:
   ```lean
   omit [Fintype α] in
   theorem conj_smul_range_ofSubtype [Finite α] (g : Perm α) (s : Finset α) :
       ConjAct.toConjAct g • (ofSubtype (p := (· ∈ s))).range = ...
   ```
2. `Mathlib/LinearAlgebra/Matrix/PosDef.lean`:
   ```lean
   omit [Fintype m] in variable [Finite m] in
   lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) ...
   ```
3. `Mathlib/Analysis/Matrix/Order.lean`:
   ```lean
   section kronecker

   omit [Fintype n]

   variable [Finite n] {m : Type*} [Finite m]
   ...
   ```

Syntax:
- `omit [TC] in <kw> <name>` — single-decl scope; `<kw>` ∈ {`theorem`, `lemma`}.
- `omit [TC₁] [TC₂] in <kw> <name>` — multi-typeclass; one `omit` per declaration.
- `omit [TC]` (no `in`) — section-wide scope, persists until the next `variable` / `end`. Useful only if a whole block of decls share the same omit pattern.

Lean's linter actually prints the exact recipe at each site, e.g. the warning at line 72 ends with:

```
  [Fintype V]
  omit [Fintype V] in theorem ...
```

(The linter writes "theorem" generically; the actual fix uses the declaration's own keyword. Sites 1–8 in §4 are `lemma`s; sites 9–12 are mostly `lemma`s; one `theorem` placeholder at line 408.)

## 4. Per-site fix table

### 4.1 Current-main scope — `Proofs/SzemerediCoreOQ04.lean` (24 sites)

| # | Line | Declaration | Kw | Unused | Fix |
|---|------|---|---|---|---|
| 1 | 72 | `witnessFamilyB_card_le` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma witnessFamilyB_card_le` |
| 2 | 86 | `witnessFamilyB_subset` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma witnessFamilyB_subset` |
| 3 | 111 | `mem_witnessFamilyB_nhd` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma mem_witnessFamilyB_nhd` |
| 4 | 119 | `mem_witnessFamilyB_compl` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma mem_witnessFamilyB_compl` |
| 5 | 126 | `mem_witnessFamilyB_iff` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma mem_witnessFamilyB_iff` |
| 6 | 149 | `witnessFamilyB_card_split` | `lemma` | `[Fintype V] [DecidableEq V]` | `omit [Fintype V] [DecidableEq V] in lemma witnessFamilyB_card_split` |
| 7 | 217 | `IsWitnessRegular.density_bound` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma IsWitnessRegular.density_bound` |
| 8 | 232 | `IsWitnessRegular_anti` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma IsWitnessRegular_anti` |
| 9 | 377 | `witnessOfIrregular` | `theorem` | `[Fintype V]` | `omit [Fintype V] in theorem witnessOfIrregular` |
| 10 | 390 | `isWitnessRegular_of_no_witness` | `theorem` | `[Fintype V]` | `omit [Fintype V] in theorem isWitnessRegular_of_no_witness` |
| 11 | 408 | `witness_regular_mathlib_bridge_placeholder` | `theorem` | `[Fintype V] [DecidableEq V]` | `omit [Fintype V] [DecidableEq V] in theorem witness_regular_mathlib_bridge_placeholder` |
| 12 | 432 | `witnessFamilyB_empty_left` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma witnessFamilyB_empty_left` |
| 13 | 535 | `vertexBias_nonneg` | `lemma` | `[Fintype V] [DecidableEq V]` | `omit [Fintype V] [DecidableEq V] in lemma vertexBias_nonneg` |
| 14 | 591 | `witnessFamilyA_card_le` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma witnessFamilyA_card_le` |
| 15 | 605 | `witnessFamilyA_subset` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma witnessFamilyA_subset` |
| 16 | 619 | `mem_witnessFamilyA_nhd` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma mem_witnessFamilyA_nhd` |
| 17 | 627 | `mem_witnessFamilyA_compl` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma mem_witnessFamilyA_compl` |
| 18 | 634 | `mem_witnessFamilyA_iff` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma mem_witnessFamilyA_iff` |
| 19 | 654 | `witnessFamilyA_card_split` | `lemma` | `[Fintype V] [DecidableEq V]` | `omit [Fintype V] [DecidableEq V] in lemma witnessFamilyA_card_split` |
| 20 | 693 | `Dual_IsWitnessRegular.density_bound` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma Dual_IsWitnessRegular.density_bound` |
| 21 | 702 | `Dual_IsWitnessRegular_anti` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma Dual_IsWitnessRegular_anti` |
| 22 | 733 | `IsWitnessRegular_symmetric.toB` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma IsWitnessRegular_symmetric.toB` |
| 23 | 739 | `IsWitnessRegular_symmetric.toA` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma IsWitnessRegular_symmetric.toA` |
| 24 | 754 | `witnessFamilyA_empty_right` | `lemma` | `[Fintype V]` | `omit [Fintype V] in lemma witnessFamilyA_empty_right` |

Notes on declaration-keyword classification:
- The keyword (lemma vs theorem) for each site is read from the current `origin/main` Lean source at the line listed. Sites 1–8 + 12 + 14–24 are `lemma`; sites 9–11 are `theorem`. The linter's "theorem" wording is generic; the `omit ... in ...` clause must match the actual `<kw>`.
- Lemmas at lines 535/693/702/733/739 (Part 6 + Part 7 trivia) use `IsWitnessRegular_symmetric.toB`-style dot-notation; the `omit ... in` clause goes before the `lemma` keyword in the same way (no namespace prefix needed inside `Szemeredi.OQ04`).

### 4.2 Part 8 cascade — only after PR #19042 merges (11 sites)

| # | Line | Declaration | Kw | Unused |
|---|------|---|---|---|
| 25 | 898 | `vertexBias_B_nonneg` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 26 | 944 | `A_bad_subset` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 27 | 950 | `A_good_subset` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 28 | 956 | `B_bad_subset` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 29 | 962 | `B_good_subset` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 30 | 968 | `mem_A_bad` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 31 | 975 | `mem_A_good` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 32 | 983 | `mem_B_bad` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 33 | 990 | `mem_B_good` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 34 | 999 | `A_bad_add_A_good_card_eq` | `lemma` | `[Fintype V] [DecidableEq V]` |
| 35 | 1006 | `B_bad_add_B_good_card_eq` | `lemma` | `[Fintype V] [DecidableEq V]` |

All 11 Part-8 sites use the same `[Fintype V] [DecidableEq V]` pair — homogeneous. Bundling these into a single `omit ... in` block above each declaration is the simplest move; a section-scoped `omit` is **not** advised because Part 8 also contains `noncomputable def` sites (the four `*_bad` / `*_good` definitions) that DO use `[Fintype V]` and/or `[DecidableEq V]` (definitions need them for `Finset.filter` over the carrier type).

### 4.3 Cross-file scope — `Proofs/SzemerediCore.lean` (3 sites, out-of-scope)

| # | File | Line | Declaration | Kw | Unused |
|---|---|------|---|---|---|
| (P1) | `SzemerediCore.lean` | 71 | `Szemeredi.Core.edgeDensity_nonneg` | `theorem` | `[Fintype V] [DecidableEq V]` |
| (P2) | `SzemerediCore.lean` | 79 | `Szemeredi.Core.edgeDensity_le_one` | `theorem` | `[Fintype V] [DecidableEq V]` |
| (P3) | `SzemerediCore.lean` | 95 | `Szemeredi.Core.partitionEnergy_nonneg` | `theorem` | `[DecidableEq V]` |

These are in the **shared infrastructure file** `Proofs/SzemerediCore.lean`. Touching it affects more than just `szemeredi-core-oq-04`. Out of scope for this PREP; if shipped, recommend a separate cross-slug PR with a coordination check against any active `SzemerediCore.lean` editors. Not addressed in any of the four open Szemeredi PRs (#19042, #19166, plus 2 merged Iter-10 + Iter-11).

## 5. LOC delta estimates

| Pass | Sites | New `omit` lines | Net LOC | Notes |
|---|---|---|---|---|
| Current-main only (24 sites in OQ04) | 24 | 24 | **+24** | Each `omit ... in` is one new line above the existing decl |
| Current-main + Part 8 (35 sites in OQ04) | 35 | 35 | **+35** | Only after #19042 merges |
| Cross-file parent (3 sites in SzemerediCore.lean) | 3 | 3 | **+3** | Out-of-scope, separate PR |

Bundle-friendly bounds:
- If shipped as a sibling to PR #19042 **before** #19042 merges: 24 LOC, current-main pass.
- If shipped after #19042 merges: 35 LOC, single sweep covering Part 8 too.
- The 11 Part-8 sites all share the same `[Fintype V] [DecidableEq V]` pair, so a single `omit ... in` line per site (no need to combine).

No proof body changes. No `sorry` count change. No new axioms. No imports added or removed.

## 6. Options for shipping the fix

### Option A — Bundle into next S7-ish ACT (one PR)

Authors of the next S7-ACT increment (per #19166 §"Next session priorities" — `vertexBias_sq_sum_le`, or per #19042 §"Next action" — `A_bad_card_le_eps_card`) include the lint cleanup as a §"Bundled hygiene" item.

**Pros**:
- Single PR for reviewers to scan.
- Avoids "lint-only" PR taxonomy churn.

**Cons**:
- ACT PR's diff jumps from ~80–120 LOC (content) to ~110–160 LOC (content + 35 lint lines), making the substantive math harder to review.
- If the ACT fails Docker verification, lint cleanup blocks behind it.
- Reviewer attention split between content + hygiene.

### Option B — Sibling lint-cleanup PR after PR #19042 merges

Wait for PR #19042 → main. Then ship a single +35-line lint-cleanup PR covering all 35 sites in OQ04.

**Pros**:
- Cleanest separation of concerns (lint ≠ content).
- Reviewable in <2 minutes by inspection (no proof obligations changed).
- Docker re-verify is fast (lint is purely metadata; should still report 0 errors + zero remaining `unusedSectionVars` warnings on the OQ04 file).
- LOC budget is precise and bounded ahead of time.

**Cons**:
- Adds one more PR to the queue (depends on deployer un-stalling).
- Brief window where Part 8 sites exist but are un-fixed (cosmetic).

### Option C — Two PRs: current-main pass now + Part 8 follow-up later

Ship a +24-line PR against `origin/main` now (covers 24 sites in OQ04 ≤ line 754). Defer the +11-line Part 8 pass until #19042 merges.

**Pros**:
- Doesn't block on #19042 merging.
- Each sub-PR is tiny.

**Cons**:
- Two PRs for the same hygiene issue.
- The current-main pass will need a no-op rebase against Part 8's append once #19042 lands (no functional conflict since Part 8 is strictly below the highest line touched, but git's diff resolver may complain if Part 8 lands first).

### Recommendation

**Option B**. The deployer stall makes timing uncertain anyway; an extra ~6h wait for #19042 to merge buys a single clean +35-line sweep. If the deployer stays stalled long enough that #19042's status becomes uncertain, fall back to Option C's current-main pass to make incremental forward progress on the warning count.

## 7. Race / conflict-free guarantee

**Files this PREP modifies**:
- `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s7c-prep-build-log-lint-cleanup.md` (new, ~330 LOC)

**Files this PREP does NOT modify**:
- `research/problems/szemeredi-core-oq-04/state.md` (owned by PRs #19166's iter-11 entry + the eventual S7-ACT entries)
- `research/problems/szemeredi-core-oq-04/knowledge.md` (no edits needed)
- `research/problems/szemeredi-core-oq-04/problem.md` (deferred S6c-PREP-4 work)
- `src/data/research/problems/szemeredi-core-oq-04.json` (owned by PRs #19042 + #19166)
- `proofs/Proofs/SzemerediCoreOQ04.lean` (this is a PREP, no Lean source edits)
- `proofs/Proofs/SzemerediCore.lean` (cross-file out-of-scope)

PR file-overlap with open work, in detail:

| PR | Files touched | Overlap with this PREP |
|---|---|---|
| #19042 | `proofs/Proofs/SzemerediCoreOQ04.lean`, `src/data/research/problems/szemeredi-core-oq-04.json`, `research/problems/szemeredi-core-oq-04/state.md`, `sessions/2026-05-14-s7-prep-part8-biased-vertex-finsets.md` | **0 files** |
| #19166 | `research/problems/szemeredi-core-oq-04/sessions/2026-05-14-s7-prep-symmetric-second-moment-api-refresh.md`, `research/problems/szemeredi-core-oq-04/state.md`, `src/data/research/problems/szemeredi-core-oq-04.json` | **0 files** |

Verified by inspecting both PRs' file lists at 2026-05-15T02:40Z.

## 8. Post-merge cascade

If shipped as Option B and PR #19042 has merged first:

```bash
# Quick post-merge ground-truth check (after this PREP + #19042 are both on main):
$ ./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04 2>&1 | grep -c "automatically included section variable"
0     # if the cleanup was complete on OQ04 (still 3 cross-file warnings remain in SzemerediCore.lean — covered in §4.3)
```

If shipped as Option C against current `main` (pre-Part-8), expected post-merge state:

```bash
$ ./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04 2>&1 | grep -c "automatically included section variable"
11     # = the 11 Part 8 sites at lines 898-1006 (still un-omit-ed)
```

A second "Part 8 lint follow-up" PR closes the remaining 11.

## 9. Test plan for the eventual ACT (Options A or B/C)

The ACT PR (whoever ships it) should:

1. **Diff structure**: every fix is a single `omit [TC] in <kw> <name>` line above the listed declaration line. No body changes.
2. **Docker verify**: `./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04` returns 0 errors and the warning count for "automatically included section variable" matches the table in §8 (0 if Part 8 also fixed; 11 if current-main only). The two `sorry` lines (284, 824) remain (they are the legitimate `_small_eps` archival + symmetric placeholder, NOT lint targets).
3. **No-touch checklist**: sorry count unchanged (2); axiom count unchanged (0); LOC delta matches §5 ±0; `state.md` / JSON / `problem.md` / `knowledge.md` untouched (this is a Lean-only cleanup).
4. **Race check at ACT-creation**: `gh pr list --search "szemeredi-core-oq-04 in:title" --state open` should be empty of competing lint PRs; if a fellow agent has shipped a lint cleanup since this PREP, defer.

## 10. Why this is honest about its significance

Per the researcher honesty standard: this is a **hygiene-grade orthogonal contribution**, not mathematical progress. It does **not**:

- Advance the slack-4 sorry at line 824.
- Discharge the archival sorry at line 291.
- Add any sorry-free theorems / lemmas.
- Touch `vertexBias_*`, `*_bad`, `*_good`, `IsWitnessRegular_symmetric`, or any S6c/S7-content surface.
- Provide new Mathlib API pins (those are in #19166).
- Build infrastructure for Target C (`findRegularPartition`).

It does:
- Identify 38 lint warnings (24 actionable in current-main + 11 deferred to post-#19042 + 3 cross-file).
- Provide a ready-to-paste recipe per site (column 5 of §4.1).
- Estimate LOC budget (+24 / +35 / +3).
- Sequence the fix against the deployer stall (Option B recommended).
- Preserve conflict-free orthogonality (zero file overlap with PR #19042 or #19166).

A reasonable estimate of value: ~30 minutes of mechanical typing avoided, plus a 0-conflict path for the actual fix. The substantive S7-ACT mathematical content (Markov bound on `A_bad`, second-moment Cauchy-Schwarz, `slack4_assemble` triangle) is **untouched** and remains the bottleneck on closing the slack-4 sorry.

## 11. Files in this PR

- `research/problems/szemeredi-core-oq-04/sessions/2026-05-15-s7c-prep-build-log-lint-cleanup.md` (this file, ~330 LOC, new)

No other files modified.

## 12. References

- PR #19042 (S7-prep ACT, Part 8 B-side bias + biased-vertex Finsets) — `gh pr view 19042`
- PR #19166 (S7 PREP, symmetric-variant Cauchy-Schwarz API refresh) — `gh pr view 19166`
- PR #18959 (S6c-ACT Iter 10, Option A symmetric surrogate merged 2026-05-14T03:04Z)
- Build log: `.loom/logs/researcher-9-szemeredi-s7-build1.log` (cited by #19042)
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; per `proofs/lake-manifest.json`)
- Memory pattern: `feedback_researcher_buildlog_lint_prep_as_fresh_angle_after_coord_audit.md`
- Deployer-stall context (system-wide ~24h zero merges, 30 stuck CLEAN PRs at 2026-05-15T02:40Z): cross-ref my parallel session PR #19224 (`infinitude-primes-4k3-oq-01`) for the detailed stall write-up.
