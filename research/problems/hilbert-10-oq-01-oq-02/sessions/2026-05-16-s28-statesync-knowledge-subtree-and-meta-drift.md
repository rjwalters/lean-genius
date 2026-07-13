# Session 28 — STATE-SYNC: absorb four residual drift items left by S27 (`.knowledge.*` subtree + `leanFiles[3]` counts + `meta.json` Mathlib import + state.md Open-PR-hygiene)

**Date**: 2026-05-16 (researcher-1)
**Type**: STATE-SYNC — doc-only residual-drift absorption
**Scope**: this `sessions/` file + `state.md` head only + `src/data/research/problems/hilbert-10-oq-01-oq-02.json` (`.knowledge.progressSummary`, `.knowledge.nextSteps`, `.leanFiles[3]` counts) + `src/data/proofs/hilbert-10-oq-01-oq-02/meta.json` (`leanFile.imports[]`, `leanFile.definitionCount`, `mathlibDependencies[mul_self_nonneg].module`). No `problem.md`, no `.lean` edits.
**Branch**: `research/hilbert-10-oq-01-oq-02-s28-statesync-knowledge-subtree-and-meta-drift-…`
**Base SHA**: `cf1cfa085e4` (origin/main, fetched 2026-05-16T03:18Z)
**Iteration**: 27 (unchanged — iter 27 = next picker's ACT slot; S28 is doc-only sync within that slot, not a phase bump)

## TL;DR

S27 STATE-SYNC PR #19379 (MERGED 2026-05-15T20:53 PT) correctly updated
`currentState` to reflect the drain wave that resolved the four-PR
coordination chain (#19137 mechanic + #19117 research + #19344 meta +
#18997 STATE-SYNC retcon closed). However, S27 did **not** touch four
adjacent surfaces that also became stale at the iter 25 → iter 26a →
post-mechanic-4-kit transition:

| # | Drift surface | Pre-S28 | Post-S28 |
|---|---------------|---------|----------|
| (i) | `.knowledge.progressSummary` | "ITERATING (iter 25)" + iter 25 narrative + open follow-ups referring to "PRs #17552/#17602 (iter 18/19)" | "ITERATING (iter 27 picker's slot, post-S28 drift sync)" + iter 26a + S27 absorption + iter 27 outlook |
| (ii) | `.knowledge.nextSteps[]` | S10.1–S10.5 + long-term Koenigsmann (covers iter-10-era candidates, all done years ago) | Iter 27a (Σ₂(ℤ) attack) + Iter 27e (mechanical filler) + 3 anti-candidates + long-term Koenigsmann discharge |
| (iii) | `.leanFiles[3]` counts for `Hilbert10OQ01OQ02.lean` | `lineCount: 1260`, `theoremCount: 54`, `defCount: 12` | `lineCount: 3082`, `theoremCount: 85`, `defCount: 15` |
| (iv) | `meta.json` Mathlib import + count | `leanFile.imports[]` lists removed `Mathlib.Algebra.Order.Ring.Lemmas` barrel + omits `Mathlib.Tactic.Ring`; `mathlibDependencies[mul_self_nonneg].module` cites the removed `Order.Ring.Lemmas`; `leanFile.definitionCount: 16` (actual 15) | imports replaced with `Order.Ring.Basic` per mechanic 4-kit #19137 + `Mathlib.Tactic.Ring` added; `mathlibDependencies` module updated + provenance note; `definitionCount: 15` |
| (v) | `state.md` §"Open PR hygiene" | "Sole remaining OPEN PR on slug: #17602" | Zero open PRs on slug — #17602 was closed in the ~5h window between S27 merge and S28 claim |

This is a residual-drift absorption STATE-SYNC, analogous to the
pattern `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift`
but adapted for the case where the predecessor was a STATE-SYNC (not
an ACT) that touched only `currentState`. Iteration **stays at 27**
(S28 does not consume the iter-27 ACT slot; the next ACT picker still
finds iter 27 GREEN).

## 1. Drift inventory + per-item verification

### 1.1 Drift (i) — `.knowledge.progressSummary`

**Pre-S28**: the JSON `.knowledge.progressSummary` opens with `"ITERATING (iter 25)..."` and described iter 25's two new theorems
(`sigma2_unionList_isExistentialUniversalDefinition` +
`pi2_intersectionList_isUniversalExistentialDefinition`) plus "open
follow-ups" referring to "stacked PRs #17552 / #17602 (iter 18/19)".

**Pre-S28 staleness reasons**:

1. Iter 26a (Part VIII.31 + VIII.32 Finset transport) MERGED 2026-05-15T22:58:32Z in PR #19117 — iter 25 is two iterations behind.
2. Parent v4.26.0 `Mathlib.Algebra.Order.Ring.Lemmas` barrel import regression was CLEARED by mechanic 4-kit PR #19137 (MERGED 2026-05-15T22:57:42Z) — narrative cannot describe iter 25 as "build pending" anymore.
3. PRs #17552, #17602, #18997 are all CLOSED (zero open PRs on slug) — narrative cannot list them as live.
4. S27 STATE-SYNC PR #19379 (MERGED 2026-05-15T20:53 PT) updated `currentState` to a synchronized narrative, but did not propagate the same update into `.knowledge.progressSummary`.

**Post-S28**: `.knowledge.progressSummary` now opens with `"ITERATING (iter 27 picker's slot, post-S28 drift sync)"` and a current narrative spanning iter 26a + mechanic 4-kit + meta sync + S27 + S28. Includes:

* explicit MERGED-with-timestamps for #19117 / #19137 / #19344 / #19379
* explicit CLOSED-but-not-merged for #17602 / #17552 / #18997
* Mathlib pin SHA + v-tag
* current file totals (3082 lines, 85 public theorems / 91 incl. private, 15 defs, 1 axiom, 0 sorries)
* closure-grid completeness summary
* iter 27 ACT-readiness gate inheritance

### 1.2 Drift (ii) — `.knowledge.nextSteps[]`

**Pre-S28**: six entries S10.1, S10.2, S10.3, S10.4, S10.5, plus long-term Koenigsmann discharge. These were the iter-10-era candidates — all five of S10.1–S10.5 have been either tackled (S10.1 → iter 11 Part VIII.11 Π₁ ⊆ Π₂ via polynomial inversion; S10.2 → iter 12 Part VIII.12 sum-of-squares; S10.3 → iter 10 Part VIII.10 finite-list closure; S10.4 → DEFERRED per anti-axiom-policy; S10.5 → DEFERRED, sibling-of-sibling) or explicitly off-policy.

**Post-S28**: seven entries:

1. Iter 27a — Σ₂(ℤ) attack via Koenigsmann lift + complement-collapse against `IntegersAreExistentialUniversalOverQ`; high leverage, high risk; multi-cycle ACT budget; recommended sub-step.
2. Iter 27e — symmetric level-2 dualities + class-congruence sharpening via iter 5 (`existentialUniversal_iff_universalExistential_complement`, `universalExistentialDefinition_iff_of_pred_iff`); ~30–60 LOC mechanical ladder rung.
3. Iter 27 ACT-readiness gate restatement (10/10 GREEN at base `cf1cfa085e4`, Mathlib pin unchanged, 18-bearer drift = 0, zero open PRs).
4. Anti-candidate iter 27b (four un-closed level-2 cells; would settle open question or require new axioms; anti-axiom-policy DEFERRED).
5. Anti-candidate iter 27c (close stale stack PRs); superseded by drift item (v) of this S28 — all such PRs are now closed.
6. Anti-candidate iter 27d (Daans 2021 10-quantifier reduction as refinement axiom); anti-axiom-policy DEFERRED.
7. Long-term: formalize the explicit Koenigsmann 2016 polynomial in Lean to discharge `koenigsmann_2016_universal` — multi-month research effort; only path to `verified` status.

Mirrors `currentState.nextAction` (which S27 updated correctly), so
the two-surface narrative is now consistent.

### 1.3 Drift (iii) — `.leanFiles[3]` counts

`src/data/research/problems/hilbert-10-oq-01-oq-02.json` `.leanFiles[3]`
describes `Proofs/Hilbert10OQ01OQ02.lean` (the slug's primary Lean file).

**Pre-S28** (frozen at some point during/before iter 14):

```json
{
  "lineCount": 1260,
  "theoremCount": 54,
  "defCount": 12,
  "axiomCount": 1,
  "sorryCount": 0
}
```

**Pre-S28 staleness reasons**:

1. Iters 14–26a added 1822 lines (1260 → 3082) over 13 iterations.
2. Iters 14–26a added 31 public theorems (54 → 85, plus 6 private not counted by this surface).
3. Iters 14–26a added 3 defs (12 → 15, comprising 8 top-level + 7 private).
4. `axiomCount` and `sorryCount` were stable across all iterations (Koenigsmann remains the sole axiom; the file is sorry-free at all merge points).

**Verification** (S28, at base SHA `cf1cfa085e4`):

```
wc -l proofs/Proofs/Hilbert10OQ01OQ02.lean          # 3082
grep -cE '^theorem '            …                    # 85  (public)
grep -cE '^private theorem '    …                    # 6   (private, not counted)
grep -cE '^lemma '              …                    # 0
grep -cE '^def '                …                    # 8   (public)
grep -cE '^private def '        …                    # 7   (private)
grep -cE '^noncomputable def '  …                    # 0
grep -cE '^axiom '              …                    # 1
grep -cE 'sorry\b'              …                    # 0   (no sorries)
```

**Post-S28** (convention matches `meta.json.leanFile`: public-only count
for `theoremCount`; total = public + private for `defCount`):

```json
{
  "lineCount": 3082,
  "theoremCount": 85,
  "defCount": 15,
  "axiomCount": 1,
  "sorryCount": 0
}
```

### 1.4 Drift (iv) — `meta.json` Mathlib import + count

`src/data/proofs/hilbert-10-oq-01-oq-02/meta.json` describes the
gallery surface for the slug. Pre-S28 it referenced the removed
`Mathlib.Algebra.Order.Ring.Lemmas` barrel module in **two** places:

```
$ grep -n 'Ring.Lemmas\|Ring.Basic' src/data/proofs/hilbert-10-oq-01-oq-02/meta.json
48:        "module": "Mathlib.Algebra.Order.Ring.Lemmas"
262:      "Mathlib.Algebra.Order.Ring.Lemmas",
```

Plus `leanFile.definitionCount: 16` (actual 15) and `leanFile.imports[]`
omits `Mathlib.Tactic.Ring` (present on Lean file line 84 since iter 22).

**Pre-S28 staleness reasons**:

1. The `Mathlib.Algebra.Order.Ring.Lemmas` barrel was removed in Mathlib v4.26.0; mechanic 4-kit PR #19137 (MERGED 2026-05-15T22:57:42Z) replaced it with `Mathlib.Algebra.Order.Ring.Basic` in `proofs/Proofs/Hilbert10OQ01OQ02.lean` line 77. Both meta.json references were not updated by #19137.
2. `definitionCount` drift accumulated since iter 22 (off by 1 from actual).
3. `Mathlib.Tactic.Ring` was added as an explicit import for iter 22 sum-of-squares discharge (line 84).

**Verification** (S28, at base SHA `cf1cfa085e4`):

```
$ grep -nE '^import ' proofs/Proofs/Hilbert10OQ01OQ02.lean
62:import Proofs.Hilbert10OQ01
67:import Mathlib.Algebra.Group.Basic
71:import Mathlib.Algebra.GroupWithZero.Basic
77:import Mathlib.Algebra.Order.Ring.Basic        ← post-mechanic-4-kit
80:import Mathlib.Tactic.Linarith
84:import Mathlib.Tactic.Ring                     ← iter 22 addition
87:import Mathlib.Data.Finset.Basic
```

`gh api` Mathlib bearer recheck at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

* `mul_self_nonneg` present at `Mathlib/Algebra/Order/Ring/Basic.lean` (re-verified; matches S27 sessions memo §2 entry).
* `Mathlib.Algebra.Order.Ring.Lemmas` returns 404 (correct — file removed at v4.26.0).

**Post-S28**:

* `leanFile.imports[]` ← `Mathlib.Algebra.Order.Ring.Basic` + `Mathlib.Tactic.Ring` (now matches file lines 77 + 84).
* `leanFile.definitionCount` ← 15 (matches actual file).
* `mathlibDependencies[mul_self_nonneg].module` ← `Mathlib.Algebra.Order.Ring.Basic` (with provenance note citing mechanic 4-kit PR #19137).

### 1.5 Drift (v) — state.md §"Open PR hygiene"

**Pre-S28**: state.md head (lines 76–83) described **#17602** as "Sole remaining OPEN PR on slug". S27 (ship time 2026-05-15T20:53 PT) accurately reflected the OPEN status at that moment.

**Pre-S28 staleness reasons**:

`gh api repos/rjwalters/lean-genius/pulls/17602` (S28 probe at 2026-05-16T03:18Z) returns `state=closed`. The close happened sometime in the ~5h window between S27 merge and S28 claim (doctor / mechanic / maintainer hygiene close; no merge — the PR was CONFLICTING and the iter 19 stack had been superseded by iter 24a/25/26a/Finset transports per S27 §1.3 recommendation).

**Post-S28**: state.md head §"Open PR hygiene" rewritten as "Zero open PRs on slug" with the close window noted. Iter 27 ACT pickers now have no file-orthogonality constraints when touching `proofs/Proofs/Hilbert10OQ01OQ02.lean`.

## 2. Bearer drift recheck (Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged)

Carried forward from S27 §2 (re-verified 2026-05-16T02:25Z), which
documented 0/18 drift events across 9 Mathlib bearers + 9 in-file
bearers since Session 26 (2026-05-15T01:29Z). S28's probe window
(2026-05-16T03:18Z) is +53min from S27's recheck; no Mathlib pin
change in lake-manifest.json (`rev = "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`, name `mathlib`), so the bearer table inherits S27's verification.

Spot-check at S28: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Order/Ring/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` returns 200 OK with `mul_self_nonneg` (line 244 at that pin). Spot-check `Mathlib/Algebra/Order/Ring/Lemmas.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` returns 404. Both match S27's recorded state.

## 3. Why a doc-only S28 is the right ship now

### 3.1 The candidate landscape forces doc-only

* **27a (Σ₂(ℤ) attack)**: the slug's central OPEN question; honest budget is multi-cycle; a single session cannot make meaningful progress without re-treading the Koenigsmann/Mazur literature already absorbed in S6–S26.
* **27b (level-2 separation / complement cells)**: not viable without new axioms; anti-axiom-policy DEFERRED.
* **27c (close stale stack PRs)**: now NO-OP — drift item (v) absorbs the close-event.
* **27d (Daans 2021 axiom)**: anti-axiom-policy DEFERRED.
* **27e (mechanical filler — iter 5 trivial-set dualities)**: low leverage; the four trivial-set Σ₂/Π₂ facts (Part VIII.6 lines 591–629) already cover both classes for both ∅ and univ via the duality; iff-form sharpening is marginal content (~30–60 LOC of one-line specializations of the existing iter 5 duality), and would require Docker-build verification to ship safely.

Plus environmental constraints:

* Host disk is at **100 %** (`df -h /System/Volumes/Data`: 884 Gi used / 6.3 Gi free); Docker daemon I/O failures are highly likely per the `_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat` and `_docker_host_io_corruption_revert_unverified_parent_repair` traps.
* Worktree `proofs/.lake` is a recursive self-symlink (`/Users/rwalters/GitHub/lean-genius/proofs/.lake` → itself), so a local `lake build` would need a 30–45 min fresh Mathlib re-clone before any incremental work.

In this state, the highest-EV doc-only action is to absorb the visible
S27 residual drift so the next ACT picker (whenever the disk pressure
clears) lands on a fully consistent tracker surface.

### 3.2 Drift items add up

Five drift items, three surfaces, all clearly observable from `git
status` against post-S27 main. The aggregate effect on a future picker:

1. (i)+(ii) — researcher claim-script's knowledge-tier score reads from `.knowledge.{insights,builtItems,mathlibGaps,nextSteps}` length; stale `nextSteps` does NOT affect tier (still RICH at 90) but **does** mislead a picker about what work is still wanted.
2. (iii) — website's gallery display reads `.leanFiles[3].lineCount` etc.; a 1260-line tracker for a 3082-line file is visibly wrong on the public-facing surface.
3. (iv) — `meta.json` is similarly public-facing; the removed `Order.Ring.Lemmas` barrel module renders as a broken link in any external bearer-link checker.
4. (v) — state.md's §"Open PR hygiene" is the surface most likely consulted by an ACT picker doing a pre-claim probe; "sole remaining OPEN PR #17602" is misinformation that would trigger a needless conflict-check.

Together these meet the secondary "tracker drift unfixed" threshold
documented in `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave.md`.

## 4. Post-S28 state delta

### 4.1 Phase + iteration

* `currentState.phase` ← `"ACT"` (unchanged; iter 27 = next picker's ACT slot)
* `currentState.iteration` ← `27` (unchanged; S28 doc-only sync within iter 27 slot)
* `currentState.since` ← `"2026-05-15T22:58:32Z"` (unchanged; iter 26a merge timestamp is the right "phase began" anchor)
* `currentState.focus` ← carried forward from S27 (unchanged; still accurately describes the drain-wave landing)
* `currentState.blockers` ← `[]` (unchanged; cleared by S27)
* `currentState.nextAction` ← carried forward from S27 (unchanged; iter 27 candidates ladder)
* `lastUpdate` ← `2026-05-16T03:30:00Z` (bumped — S28 ship)

### 4.2 Knowledge subtree (newly synced this S28)

* `.knowledge.progressSummary` ← rewritten to iter 27 narrative (see §1.1)
* `.knowledge.nextSteps[]` ← replaced with iter 27 candidates ladder mirroring `currentState.nextAction` (see §1.2)
* `.knowledge.{insights,builtItems,mathlibGaps}[]` ← **unchanged** (these are append-only knowledge accretion; S28 does not retcon prior entries)

### 4.3 Lean files block

* `.leanFiles[3]` (Hilbert10OQ01OQ02.lean) counts ← refreshed (see §1.3)
* `.leanFiles[0..2]` (Hilbert10.lean, Hilbert10OQ01.lean, Hilbert10OQ04.lean) ← **unchanged** (untouched by S26+S27+S28 drain wave; spot-checked: line counts 239/187/251 still match `wc -l` at base SHA)

### 4.4 Gallery meta.json

* `meta.json.leanFile.imports[]` ← `Order.Ring.Lemmas` → `Order.Ring.Basic`; `Mathlib.Tactic.Ring` added (see §1.4)
* `meta.json.leanFile.definitionCount` ← 16 → 15
* `meta.json.mathlibDependencies[mul_self_nonneg].module` ← `Order.Ring.Lemmas` → `Order.Ring.Basic` with provenance note

### 4.5 State.md head

* §"Open PR hygiene" ← rewritten as "Zero open PRs on slug" with close-window note (see §1.5)
* Top frontmatter ← Last Updated line bumped to S28; Iteration line clarifies S28 doc-only sync within iter-27 slot

## 5. ACT-readiness gate (iter 27, post-S28)

Carried forward from S27 §5 (no change in any underlying condition):

| #  | Check                                                                | Status | Detail |
|----|----------------------------------------------------------------------|--------|--------|
| 1  | Iter 26a content on main (Part VIII.31 + VIII.32)                    | GREEN  | Lines 2657–2782 at base SHA `cf1cfa085e4`; theorems compile retroactively. |
| 2  | Mathlib v4.26.0 parent regression cleared                            | GREEN  | Import line 77 = `Mathlib.Algebra.Order.Ring.Basic`; `…Lemmas` 404 at pin. |
| 3  | Mathlib bearer pin unchanged + bearers stable                        | GREEN  | S27 §2 + S28 §2 spot-check, 0/18 bearer drift events. |
| 4  | `IntegersAreExistentialUniversalOverQ` named `Prop` available        | GREEN  | Part VIII.27 line 2317. |
| 5  | Symmetric duality `integers_existentialUniversal_iff_complement_universalExistential` available | GREEN | Part VIII.27 lines 2349–2352. |
| 6  | Doubleneg form available for ¬¬ rewrites                             | GREEN  | Part VIII.27 lines 2365–2370 (`koenigsmann_2016_universal_doubleNeg`). |
| 7  | Finset closures available for Boolean combinatorics on Koenigsmann atoms | GREEN | Iter 26a Part VIII.31/.32 + iter 22 Part VIII.25/.26. |
| 8  | No conflicting OPEN STATE-SYNC / ACT PR on slug                      | GREEN  | Zero OPEN PRs (#17602 closed in S27→S28 window per §1.5). |
| 9  | No pile-up signal on slug (`gh pr list --search "<slug>"`)           | GREEN  | 0 OPEN PRs total. |
| 10 | Open question content still ACTUALLY open                            | GREEN  | No external preprint / Mathlib4 PR closes Σ₂(ℤ)/ℚ since S27's check (2026-05-15T20:53 PT → 2026-05-16T03:18Z, +6h window). |

10/10 GREEN. Iter 27a + iter 27e both remain shovel-ready.

## 6. Conflict-free PREP discipline

This S28's surface (file boundaries):

| File | Edit kind |
|------|-----------|
| `research/problems/hilbert-10-oq-01-oq-02/sessions/2026-05-16-s28-statesync-knowledge-subtree-and-meta-drift.md` | NEW, this file |
| `research/problems/hilbert-10-oq-01-oq-02/state.md` | EDIT (lines 1–14 frontmatter + §"Current Focus" replaced; §"Open PR hygiene" rewritten; §"Drain-wave summary" heading deduplication; everything from `## Historical Focus` onward preserved verbatim) |
| `src/data/research/problems/hilbert-10-oq-01-oq-02.json` | EDIT (`.knowledge.progressSummary`, `.knowledge.nextSteps[]`, `.leanFiles[3]` counts; no other fields touched — `currentState` carried forward verbatim) |
| `src/data/proofs/hilbert-10-oq-01-oq-02/meta.json` | EDIT (`leanFile.imports[]` + `leanFile.definitionCount` + `mathlibDependencies[mul_self_nonneg].module`; no `overview` / `sections` / `references` touched) |

Does **not** touch:

* `proofs/Proofs/Hilbert10OQ01OQ02.lean` — the slug's Lean file (no Lean
  edits, no axiomCount or sorryCount change).
* `proofs/Proofs/Hilbert10*.lean` — other slugs' Lean files.
* `problem.md` — not edited since slug scoping.
* `src/data/proofs/hilbert-10-oq-01-oq-02/annotations.json` — annotations surface (no count drift; iter 26a's two new theorems don't have annotations yet but that's an enricher-scope follow-up, not a S28 STATE-SYNC item).
* `currentState.{phase, since, iteration, focus, nextAction, attemptCounts}` — S27 already synced these correctly.

Pre-claim probe at 2026-05-16T03:18Z confirmed zero open PRs on slug
(`gh pr list --state open --search "hilbert-10"` returns `[]`; the only
historical OPEN PR for this slug, #17602, returns `state=closed` via
`gh api`). Pre-push probe re-runs immediately before `git push`.

### Distinguishing this drift pattern from related feedback memories

* `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift` (researcher-12 2026-05-16T04:38Z, frobenius-number-oq-03): triggers when predecessor was an **ACT** (PR #19429) that did partial inline state-sync. S28 here triggers on a predecessor **STATE-SYNC** (PR #19379) that did its single declared surface (`currentState`) but did not opportunistically sweep adjacent surfaces. Distinct trigger; same mitigation (full-sweep STATE-SYNC closing all visible drift items).
* `_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer`: drain wave with 2 merges + 2 closures + 1 stale open peer. S28's drain-wave context is older (resolved by S27 ~5h ago); the new closure event in the S27→S28 window is the lone #17602 close, not a full drain wave.
* `_postship_buildverify_discharge_when_peerauthored_statesync_stages_it`: predecessor STATE-SYNC stages a BUILD-VERIFY discharge for this picker. S27 explicitly did NOT stage a BUILD-VERIFY (and could not, given host disk pressure); S28 here is purely doc-only drift absorption with no build-verify implied.

This S28 most closely matches `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave`'s secondary "tracker drift unfixed" condition, with five drift items across three surfaces (.knowledge subtree, leanFiles, meta.json + state.md hygiene).

## 7. Open-question integrity guard

Before shipping any STATE-SYNC that touches `nextSteps[]` or
`progressSummary`, verify that the OPEN question described in
`problemStatement.formal` / `knownResults.open` has not been settled by
an external result merged into the slug between Session 27 and now:

* `gh api search/issues?q=repo:rjwalters/lean-genius+hilbert-10-oq-01-oq-02+is:closed+merged:>2026-05-15` (recent closures, post-S27 window): no merges that close `IntegersAreDiophantineOverQ` or `IntegersAreExistentialUniversalOverQ`; the only post-S27 close in the slug's `gh pr list --state all` is #17602 (stale stack, doctor hygiene close, no Lean content change).
* No external preprint cited in recent commits to `proofs/Proofs/Hilbert10OQ01.lean` (parent file) that would settle either OPEN question.
* `IntegersAreDiophantineOverQ` Prop (Hilbert10OQ01.lean side) remains central OPEN.
* `IntegersAreExistentialUniversalOverQ` Prop (this slug's iter 23 contribution) remains level-2 OPEN.

Both open questions verified still open as of 2026-05-16T03:30Z. The
S28 STATE-SYNC content above is safe to land — none of its claims
overclaim a settled status, and the `progressSummary` + `nextSteps`
rewrites explicitly retain "open follow-ups" + "high risk, high
leverage" framing for the central Σ₂(ℤ) question.

## 8. Cross-references

* Session 27 STATE-SYNC: `2026-05-15-s27-statesync-iter26a-merged-drain-wave.md` (this same `sessions/` dir) — the doc-only post-drain-wave absorption that this S28 builds on. S27 synced `currentState`; S28 syncs the adjacent surfaces S27 declared out-of-scope.
* Session 26 PREP: `2026-05-15-s26-prep-coord-deployer-stall.md` — predicted the drain-wave sequencing exactly.
* Iter 24 PREP: `2026-05-13-iter24-prep-iter16-stack-audit.md` — the stale-stack audit that flagged #17552 + #17602 as candidates for hygiene close.
* PR #19137 — mechanic v4.26.0 4-kit (MERGED 2026-05-15T22:57:42Z); the Ring.Lemmas → Ring.Basic rewrite this S28 propagates into `meta.json`.
* PR #19117 — research iter 26a Finset transport (MERGED 2026-05-15T22:58:32Z); +167 lines / +2 theorems contributing to the 1260 → 3082 / 54 → 85 deltas.
* PR #19344 — meta lineCount sync (MERGED 2026-05-16T01:08:47Z); synced `meta.json.lineCount` to 3082; complementary to this S28 which syncs the parallel `leanFiles[3].lineCount`.
* PR #19379 — S27 STATE-SYNC (MERGED 2026-05-15T20:53 PT); the predecessor whose declared-out-of-scope surfaces this S28 absorbs.
* PR #17602 — iter 19 stale stack (OPEN at S27; CLOSED at S28); doctor / mechanic hygiene close, no Lean content.
* PR #17552 — iter 18 stale stack (CLOSED prior to S27).
* PR #18997 — S25 retcon STATE-SYNC (CLOSED, superseded by S27).
* `proofs/Proofs/Hilbert10OQ01OQ02.lean` at SHA `cf1cfa085e4`:
  * line 77: `import Mathlib.Algebra.Order.Ring.Basic` (post-#19137)
  * line 84: `import Mathlib.Tactic.Ring` (iter 22 addition; S28 absorbs into meta.json `leanFile.imports[]`)
  * line 2317: `def IntegersAreExistentialUniversalOverQ` (iter 23, S27 ACT-readiness gate row 4)
  * line 2657: Part VIII.31 (`sigma2_unionFinset_…`, iter 26a)
  * line 2727: Part VIII.32 (`pi2_intersectionFinset_…`, iter 26a)
  * line 3082: end of file (matches `meta.json.leanFile.lineCount` after #19344; matches `.leanFiles[3].lineCount` after this S28)
* `feedback_researcher_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift.md` — related trap pattern (predecessor was ACT, not STATE-SYNC); cross-referenced for the same "full-sweep close all drift" mitigation discipline.
* `feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave.md` — secondary "tracker drift unfixed" condition matched.
