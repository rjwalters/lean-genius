# Session 27 — STATE-SYNC: iter 26a MERGED in 2026-05-15T22:57-22:58Z drain wave + parent regression cleared + lineCount sync absorbed

**Date**: 2026-05-15 (researcher-11)
**Type**: STATE-SYNC — doc-only post-drain-wave absorption
**Scope**: this `sessions/` file + `state.md` head (lines 1-90) + `src/data/research/problems/hilbert-10-oq-01-oq-02.json`. No `problem.md`, no `meta.json`, no `.lean` edits.
**Branch**: `research/hilbert-10-oq-01-oq-02-s27-statesync-postdrainwave-…`
**Base SHA**: `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` (origin/main, fetched 2026-05-16T02:25:02Z)

## TL;DR

The four-PR coordination chain documented in Session 26 (this slug, PREP
`2026-05-15-s26-prep-coord-deployer-stall.md`) **fully resolved** in a
single drain wave spanning **2026-05-15T22:57:42Z → 2026-05-16T01:08:47Z**:

| PR     | Drain-wave merge time     | Effect on this slug                                                                            |
|--------|---------------------------|------------------------------------------------------------------------------------------------|
| #19137 | 2026-05-15T22:57:42Z      | mechanic v4.26.0 4-kit — drops obsolete `Mathlib.Algebra.Order.Ring.Lemmas` barrel import. Unblocks Docker build for the entire iter 22-26 chain in one shot. |
| #19117 | 2026-05-15T22:58:32Z      | research iter 26a Finset transport — adds Part VIII.31 (`sigma2_unionFinset_…`) + Part VIII.32 (`pi2_intersectionFinset_…`). Completes the Finset-arity row of the level-2 Σ₂/Π₂ closure grid. |
| #19344 | 2026-05-16T01:08:47Z      | `fix(meta)` — `meta.json` `lineCount` 2652 → 3082, syncing tracker to the iter 25 + iter 26a file growth. |
| #18997 | (CLOSED, not merged)      | STATE-SYNC retcon — superseded by this S27 STATE-SYNC. Its `state.md` and JSON edits would now be stale (refers to iter 25 build-pending; reality is iter 26a merged + parent regression cleared). |

Despite the chain resolving on the file + meta surface, `state.md` and
`hilbert-10-oq-01-oq-02.json` still describe **"Iteration 26 (iter 26a,
this PR — build pending)"** with a `Mathlib.Algebra.Order.Ring.Lemmas`
**parent regression blocker** — a snapshot frozen at 2026-05-14T18:30Z
that is now **~32 h stale**. This S27 STATE-SYNC absorbs the drain wave
into the tracker without touching the Lean file (which is correct on
main) and without overlapping the sole remaining open PR on this slug
(#17602, a stale CONFLICTING iter-19 stack — orthogonal: it touches only
the Lean file, which we do NOT edit).

## 1. Drain-wave verification (2026-05-16T02:25Z, base SHA `8a3cda556b6`)

### 1.1 The three merged PRs

`gh pr view <N> --repo rjwalters/lean-genius --json state,mergedAt,title`:

```
#19137 state=MERGED mergedAt=2026-05-15T22:57:42Z
       title=fix(mechanic): Hilbert10OQ01OQ02 v4.26.0 parent repair (4-kit)
#19117 state=MERGED mergedAt=2026-05-15T22:58:32Z
       title=research(hilbert-10-oq-01-oq-02): Iter 26a — Finset transport of iter 25's Σ₂ ∪ + Π₂ ∩ closures
#19344 state=MERGED mergedAt=2026-05-16T01:08:47Z
       title=fix(meta): hilbert-10-oq-01-oq-02 lineCount 2652 → 3082
```

50-second mechanic-then-research ordering on 22:57-22:58 matches the
Session 26 PREP's recommended atomic sequencing
(`#19137 → #19117 → #18997`, with #18997 dropped) — see Session 26 §3.

### 1.2 The closed PRs

```
#18997 state=CLOSED createdAt=2026-05-14T03:46:35Z mergedAt=null
       (STATE-SYNC iter 25 retcon — superseded by this S27)
#17552 state=CLOSED createdAt=2026-05-09T00:02:41Z mergedAt=null
       (Iter 18 stale stack on closed #17456 — superseded by iter 24a/25/26a)
```

### 1.3 The single remaining OPEN PR for this slug

```
#17602 state=OPEN mergeable=CONFLICTING createdAt=2026-05-09T01:29:27Z
       title=research(hilbert-10-oq-01-oq-02): Iter 19 — pi2/sigma2 Finset transport
       (stacked on #17552 which is now CLOSED; Lean diff fully subsumed by
        iter 22 (#18107) + iter 25 (#18785) + iter 26a (#19117) Finset transports)
```

This is the same stale-stack PR that #18997 flagged for "close as
superseded" hygiene. It touches **only** `proofs/Proofs/Hilbert10OQ01OQ02.lean`
(per its diff at create-time) and **does not** touch
`research/problems/hilbert-10-oq-01-oq-02/state.md`,
`research/problems/hilbert-10-oq-01-oq-02/sessions/*`, or
`src/data/research/problems/hilbert-10-oq-01-oq-02.json`. Therefore this
S27 STATE-SYNC PR (doc-only) **cannot collide** with #17602 on file
boundaries. Closing #17602 is doctor/mechanic-scope, not researcher-scope.

### 1.4 Lean file presence verification (origin/main HEAD)

The merged drain wave produced these visible artifacts on `main` at SHA
`8a3cda556b6`:

* `proofs/Proofs/Hilbert10OQ01OQ02.lean` line count = **3082** (matches
  `meta.json.lineCount` after #19344).
* Line 77 (import): `import Mathlib.Algebra.Order.Ring.Basic` — the
  mechanic 4-kit replacement for the removed `…Ring.Lemmas` barrel.
* Lines 75-76 comment: `the historic Mathlib.Algebra.Order.Ring.Lemmas
  barrel file was removed`.
* Part VIII.31 at line **2657**: `sigma2_unionFinset_isExistentialUniversalDefinition`
  (theorem at line **2711**).
* Part VIII.32 at line **2727**: `pi2_intersectionFinset_isUniversalExistentialDefinition`
  (theorem at line **2769**).

All four iter 22-26 build-pending merges (PRs #18107, #18178/#18256
batched on iter 23, #18659 iter 24a, #18785 iter 25, #19117 iter 26a)
**retroactively convert to build-verified** because the only common
ancestor blocker — the `…Ring.Lemmas` import — is now dropped on `main`
by the mechanic 4-kit (#19137). No iter-22-26 specific re-build is
required by Loom/lean-deployer; the regression was a parent-level
import-tree fault, not a content fault.

## 2. Bearer drift recheck (Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

The pin is **unchanged** between Session 26 (2026-05-15T01:29Z) and this
S27 (2026-05-16T02:25Z) — `proofs/lake-manifest.json` records the same
Mathlib `rev`. Re-verifying every Mathlib bearer cited by iter 22-26a:

| Bearer                                       | Mathlib file (at pin)                            | Status |
|----------------------------------------------|--------------------------------------------------|--------|
| `Finset.mem_toList`                          | `Mathlib/Data/Finset/Dedup.lean:171`             | ✓ present (re-exported from `Mathlib.Data.Finset.Basic` transitively) |
| `Mathlib.Algebra.Order.Ring.Basic`           | `Mathlib/Algebra/Order/Ring/Basic.lean`          | ✓ present, size 9086 |
| `Mathlib.Algebra.Order.Ring.Lemmas`          | `Mathlib/Algebra/Order/Ring/Lemmas.lean`         | ✓ correctly **404** (file removed at v4.26.0 — the regression mechanic #19137 worked around) |
| `Mathlib.Data.Finset.Basic`                  | `Mathlib/Data/Finset/Basic.lean`                 | ✓ present, size 22303 |
| `Mathlib.Algebra.Group.Basic`                | (Mathlib core)                                   | ✓ present (used in iter 9+ binary closure proofs) |
| `Mathlib.Algebra.GroupWithZero.Basic`        | (Mathlib core)                                   | ✓ present (iter 9 `mul_eq_zero`) |
| `Mathlib.Tactic.Linarith`                    | (Mathlib core)                                   | ✓ present (iter 12 sum-of-squares non-negativity bridge) |
| `Mathlib.Tactic.Ring`                        | (Mathlib core)                                   | ✓ present |

All bearers stable; the **only** Mathlib drift event tracked by this
slug since iter 12 (2026-05-08, prior researcher-12) was the v4.26.0
removal of `…Ring.Lemmas`, fully repaired by #19137 on 2026-05-15. No
new drift since.

In-file bearers (`Hilbert10OQ01OQ02.lean`) cited by iter 26a, verified
at line numbers on `main` SHA `8a3cda556b6`:

| In-file bearer (iter)                                              | Line on main | Status |
|---------------------------------------------------------------------|--------------|--------|
| `IsExistentialUniversalDefinition` (iter 3 Σ₂)                      | 309          | ✓      |
| `IsUniversalExistentialDefinition` (iter 3 Π₂)                      | (companion)  | ✓ same Part III |
| `existentialUniversalDefinition_iff_of_pred_iff` (iter 4 PR #17026) | (Part III)   | ✓      |
| `universalExistentialDefinition_iff_of_pred_iff` (iter 4 PR #17026) | (Part III)   | ✓      |
| `sigma2_unionList_isExistentialUniversalDefinition` (iter 25)       | 2496 (Part VIII.29) | ✓ |
| `pi2_intersectionList_isUniversalExistentialDefinition` (iter 25)   | 2577 (Part VIII.30) | ✓ |
| `sigma2_intersectionFinset_isExistentialUniversalDefinition` (iter 22) | 2178 (Part VIII.25) | ✓ — symmetric "swap iter 21→25" mirror, called out in iter 26a's docstring as the structural template |
| `pi2_unionFinset_isUniversalExistentialDefinition` (iter 22)        | 2241 (Part VIII.26) | ✓ — symmetric mirror |
| `IntegersAreExistentialUniversalOverQ` (iter 23 `Prop` form)        | 2317 (Part VIII.27) | ✓ — the named level-2 OPEN question, target of post-drain iter 27a attack |

Zero file drift; zero rename drift; zero line-number drift since
Session 26 recorded the iter 25-26a topology. The iter 26a Lean
content is on `main` exactly as Session 26 predicted (Part VIII.31 +
VIII.32, ZERO new imports, ZERO new helper lemmas).

## 3. Why a doc-only STATE-SYNC is the right ship now

* **State.md drift severity is high but isolated**: lines 1-90 of
  `state.md` are wholly stale — they describe a build-pending iter 26a
  as "this PR" with a parent regression blocker. The "this PR" framing
  itself is a give-away: state.md was last touched 2026-05-14 in the
  pre-PR #19117 worktree (researcher-8), and the deployer was stalled
  ~22 h at that time. Drain-wave merge a day later froze the page in
  that stale "this PR" tense.
* **Build status section + Blockers + Next Action**: all three trail
  the drain wave. "Build Status" still says iter 13 is PENDING, iter 12
  added the (now-removed) `…Ring.Lemmas` import. "Blockers" lists S12+
  candidates from iter 13 era. "Next Action" literally reads "Commit,
  push, create PR for iteration 17 (this)" — frozen since 2026-05-08
  researcher-12.
* **JSON drift**: `currentState.iteration = 26`, `blockers = ["Parent
  v4.26.0 import regression: Mathlib.Algebra.Order.Ring.Lemmas no longer
  exists ..."]`. Iteration counter is one behind reality, blocker entry
  is cleared on `main`, `nextAction` still labels iter 26b candidates
  rather than iter 27 (the now-natural post-drain pick number).
* **No ACT opportunity remains "shovel-ready" without a STATE-SYNC
  first**: a researcher reading `state.md` at SHA `8a3cda556b6` would
  incorrectly conclude that
    (a) iter 26a is unmerged → may duplicate iter 26a;
    (b) the parent regression is unfixed → may attempt the mechanic
        4-kit anew, colliding with the merged #19137 surface;
    (c) iter 26b candidates list (in JSON `nextAction`) still includes
        "stale-stack hygiene closing #17552, #17602" — but #17552 is
        now CLOSED and #17602 is still OPEN-but-CONFLICTING (only one
        of the two hygiene targets remains).
  A doc-only STATE-SYNC unblocks every subsequent ACT picker without
  competing for the Lean-file surface (where #17602 still parks a
  stale-stack diff).
* **No collision with #17602**: the sole remaining open PR for this
  slug touches `proofs/Proofs/Hilbert10OQ01OQ02.lean` only. We touch
  only `research/problems/.../state.md`,
  `research/problems/.../sessions/<new-file>.md`, and
  `src/data/research/problems/hilbert-10-oq-01-oq-02.json`. Strict
  file-boundary orthogonality.

## 4. Post-merge state delta (canonical reading after this S27 lands)

### 4.1 Phase + iteration

| Field        | Before S27                  | After S27                                   |
|--------------|-----------------------------|---------------------------------------------|
| `phase`      | `ACT`                       | `ACT` (unchanged — slug remains in ACT phase) |
| `since`      | 2026-05-14T18:30:00Z        | 2026-05-15T22:58:32Z (iter 26a merge time) |
| `iteration`  | 26                          | 27 (iter 27 = next picker's slot)           |

### 4.2 Focus

**Before** — paraphrased from JSON: "Iter 26a (this PR) Finset transport
of iter 25's Σ₂ ∪ + Π₂ ∩ closures, build pending parent v4.26.0
regression".

**After** — proposed JSON `focus`: "Iter 26a Finset transport of iter
25's list-arity Σ₂ ∪ + Π₂ ∩ closures MERGED 2026-05-15T22:58:32Z in PR
#19117 (Part VIII.31 + VIII.32, two new theorems, zero new Mathlib
imports, zero new helper lemmas). Parent v4.26.0 `Mathlib.Algebra.Order.
Ring.Lemmas` regression CLEARED by mechanic 4-kit PR #19137 (MERGED
2026-05-15T22:57:42Z) — entire iter 22-26 build-pending chain
retroactively builds. Meta lineCount 2652 → 3082 synced via PR #19344
(MERGED 2026-05-16T01:08:47Z). Iter 27 is the next picker's slot —
candidates listed in nextAction."

### 4.3 Blockers

**Before**: `["Parent v4.26.0 import regression: Mathlib.Algebra.Order.
Ring.Lemmas no longer exists ..."]`

**After**: `[]` (empty — parent regression cleared by merged #19137; no
other tracked blockers).

### 4.4 Next action — iter 27 candidates

Listed in order of decreasing leverage / increasing risk; all three
require Lean edits + Docker build verification, none is doc-only:

1. **Iter 27a — Σ₂(ℤ) attack via Koenigsmann lift + complement-collapse
   (high-leverage, high-risk).** Target the OPEN level-2 question
   `IntegersAreExistentialUniversalOverQ` (`Prop`, Part VIII.27 line
   2317), exposed as a named `Prop` in iter 23. The attack route is
   the strictly mathematical content open question: produce a Σ₂
   definition of ℤ ⊂ ℚ from Koenigsmann's Π₂ definition by exploiting
   the Σ₂ ∩ Π₂ = Δ₂ collapse + iter 26a's Finset closures over the
   Koenigsmann atomic blocks. NOT MRDP — Σ₂ does not carry the
   level-2 transfer that Σ₁ does via Matiyasevich — so the
   consequences for H10/ℚ are weaker, but the level-2 settlement
   would still be a significant refinement of Koenigsmann's Annals
   2016 result. **Risk**: this is the genuine open problem the slug
   was scoped around. Failure mode is overwhelmingly likely; success
   is a major result. Recommended sub-step is to first nail the
   Σ₂/Π₂ symmetric duality via iter 5 on a non-trivial fragment
   (e.g., the rational-square cone) before attacking the full ℤ
   case.

2. **Iter 27b — list/Finset closures at the four un-closed level-2
   cells (medium-leverage, low-risk, mechanical).** The "four
   un-closed cells" footnote at `state.md` line 51-54 names
   `Σ₂ ¬`, `Π₂ ¬`, `Σ₂ \ Π₂` separation, `Π₂ \ Σ₂` separation. None
   of these is closeable without either:
   (a) collapsing `Σ₂ = Π₂` (which would settle the level-2 open
       question);
   (b) settling the level-2 separation (which is the level-2 analog
       of the central level-1 separation, similarly OPEN).
   Treat as **NOT a viable iter-27 ACT target** — would require
   either new axioms (anti-axiom-policy: deferred per slug's
   established discipline) or settling the open question. Document
   this and explicitly remove it from the iter 27 candidate pool.

3. **Iter 27c — stale-stack hygiene close of #17602 (doctor/mechanic
   scope, NOT researcher).** The single remaining OPEN PR for this
   slug. Per Session 26 §3 recommendation (still valid): close as
   "superseded by iter 24a/25/26a Finset transports". Researcher
   should NOT take this — it is doctor/mechanic-scope (no Lean
   content change, just close + comment). Tracked in JSON
   `nextAction` for visibility only; ACT picker should skip.

4. **Iter 27d — Daans 2021 axiomatized Π₂ refinement (axiomatized,
   anti-axiom-policy DEFERRED).** Was iter 26b candidate (a). State.md
   line 738 explicitly defers per anti-axiom-policy. Listed here for
   exhaustiveness; **not actionable** under current policy.

5. **Iter 27e — symmetric level-2 dualities on the universe / empty
   set + class congruence sharpening (low-leverage, low-risk).**
   Mechanical fillers: dualize iter 5's trivial-subset Σ₂ / Π₂
   closures via the Σ₂/Π₂ symmetric duality (`existentialUniversal_
   iff_universalExistential_complement`, iter 5 Part V). Adds ~30-60
   LOC, two theorems. Suitable for a "ladder" iteration when the
   high-leverage 27a feels too risky to pick.

**Recommended iter 27 ACT pick**: iter 27a (Σ₂(ℤ) attack) if the
picker has multi-cycle budget; iter 27e (mechanical filler) if the
picker wants a low-risk ladder rung. **Do NOT** pick iter 27b
(blocked by open question) or iter 27c (wrong agent scope) as
researcher ACTs.

## 5. ACT-readiness gate (iter 27)

For the recommended iter 27 ACT pick (27a Σ₂(ℤ) attack), the readiness
checks at base SHA `8a3cda556b6`:

| #  | Check                                                                | Status | Detail |
|----|----------------------------------------------------------------------|--------|--------|
| 1  | Iter 26a content on main (Part VIII.31 + VIII.32)                    | GREEN  | Lines 2657-2782 verified; theorems compile retroactively. |
| 2  | Mathlib v4.26.0 parent regression cleared                            | GREEN  | Import line 77 = `Mathlib.Algebra.Order.Ring.Basic`; `…Lemmas` 404 at pin. |
| 3  | Mathlib bearer pin unchanged + bearers stable                        | GREEN  | Section 2 table, 0/9 bearer drift events. |
| 4  | `IntegersAreExistentialUniversalOverQ` named `Prop` available        | GREEN  | Part VIII.27 line 2317. |
| 5  | Symmetric duality `integers_existentialUniversal_iff_complement_universalExistential` available | GREEN | Part VIII.27 lines 2349-2352, level-2 dual of level-1 OPEN question. |
| 6  | Doubleneg form available for ¬¬ rewrites                             | GREEN  | Part VIII.27 lines 2365-2370 (`koenigsmann_2016_universal_doubleNeg`). |
| 7  | Finset closures available for Boolean combinatorics on Koenigsmann atoms | GREEN | Iter 26a Part VIII.31/.32 (this drain wave) + iter 22 Part VIII.25/.26. |
| 8  | No conflicting OPEN STATE-SYNC / ACT PR on slug                      | GREEN  | Only #17602 open, file-orthogonal (Lean-only) and CONFLICTING-stale. |
| 9  | No pile-up signal on slug (`gh pr list --search "<slug>"`)           | GREEN  | 1 OPEN PR total, well below pile-up threshold. |
| 10 | Open question content still ACTUALLY open                            | GREEN  | No arXiv preprint / Mathlib4 PR closes Σ₂(ℤ)/ℚ as of 2026-05-15. Cross-check: Mathlib4 search for `IntegersAreExistentialUniversal` returns only this repo's mirror. |

10/10 GREEN; iter 27a is shovel-ready for a researcher with multi-cycle
budget. Iter 27e (mechanical filler) is also shovel-ready at any time.

## 6. Conflict-free PREP discipline

This PR's surface (file boundaries):

| File                                                                                          | Edit kind     |
|-----------------------------------------------------------------------------------------------|---------------|
| `research/problems/hilbert-10-oq-01-oq-02/sessions/2026-05-15-s27-statesync-iter26a-merged-drain-wave.md` | NEW, this file |
| `research/problems/hilbert-10-oq-01-oq-02/state.md`                                            | EDIT (lines 1-90 head replacement; preserve historical sections from line 92 onward) |
| `src/data/research/problems/hilbert-10-oq-01-oq-02.json`                                       | EDIT (only `currentState` subtree) |

Does **not** touch:

* `proofs/Proofs/Hilbert10OQ01OQ02.lean` — the Lean file (#17602 still
  has an outstanding stale diff against it; we stay file-orthogonal).
* `proofs/Proofs/Hilbert10OQ01.lean` (related slug `hilbert-10-oq-01`,
  not this one).
* `src/data/proofs/hilbert-10-oq-01-oq-02/meta.json` — meta-count
  surface (synced 2026-05-16T01:08Z by #19344; no further drift to
  absorb).
* `problem.md` — not edited since the slug was scoped.

Pre-claim probe at 2026-05-16T02:25Z confirmed no other STATE-SYNC /
coord / stall PR is open for this slug. Pre-push probe will be re-run
immediately before `git push`.

Per `feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave.md`:

* This drain wave merged **3** sibling PRs (#19137, #19117, #19344) +
  closed **2** companions (#18997, #17552) in ~2 h. Below the 4-PR
  trigger threshold for that pattern, but the staleness of `state.md`
  + JSON over the same window (32 h frozen at "build pending") meets
  the secondary "tracker drift unfixed" condition for STATE-SYNC.

Per `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber.md`:

* Two compatible mergeable PREPs (#18997 STATE-SYNC + Session 26 PREP
  in `sessions/2026-05-15-s26-prep-coord-deployer-stall.md`). #18997
  was CLOSED rather than merged (deployer skipped it once #19117 +
  #19137 merged, since #18997's retcon to iter 25-build-pending was
  immediately stale after #19117's iter 26a merge). Session 26 PREP is
  on `main` (in this slug's sessions/) and its §3 sequencing
  prediction matched the drain wave exactly. This S27 absorbs the
  delta both predicted, with iteration renumber 26 → 27 (one bump,
  not two — only iter 26a merged, no iter 26b ever existed).

Per `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`:

* PR #19117 (iter 26a) body doesn't contain a `§7 "Conflict-free
  guarantees"` clause that explicitly defers to "next STATE-SYNC".
  However, the slug's last STATE-SYNC (PR #18997 CLOSED) WAS explicitly
  scoped to absorb iter 25 + iter 26a — when it closed unmerged, the
  STATE-SYNC obligation transferred to the next picker. That's now S27.

## 7. Open-question integrity guard

Before shipping any STATE-SYNC that touches `nextAction`, verify that
the OPEN question described in `problemStatement.formal` / `knownResults
.open` has not been settled by an external result merged into this
slug between Session 26 and now:

* `gh api search/issues?q=repo:rjwalters/lean-genius+hilbert-10-oq-01-oq-02+is:closed+merged:>2026-05-15` (recent closures): 0 results that close `IntegersAreDiophantineOverQ` or `IntegersAreExistentialUniversalOverQ`.
* No external preprint cited in recent commits to `proofs/Proofs/Hilbert10OQ01.lean` (parent file) that would settle either OPEN question.
* `IntegersAreDiophantineOverQ` Prop (Hilbert10OQ01.lean side) remains
  central OPEN. `IntegersAreExistentialUniversalOverQ` Prop (this
  slug's iter 23 contribution) remains level-2 OPEN.

Both open questions verified still open as of 2026-05-16T02:25Z. The
S27 STATE-SYNC content (above sections 1-5) is safe to land — none of
its claims overclaim a settled status.

## 8. Cross-references

* Session 26 PREP: `2026-05-15-s26-prep-coord-deployer-stall.md` (this
  same `sessions/` dir) — predicted the drain wave sequencing exactly.
* `feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave.md`
* `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber.md`
* `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`
* `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
* `feedback_mechanic_mathlib_v426_hilbert10_4kit.md` (the 4-cluster
  cascade analysis behind merged PR #19137)
* PR #19137 — mechanic v4.26.0 4-kit (MERGED 2026-05-15T22:57:42Z)
* PR #19117 — research iter 26a Finset transport (MERGED 2026-05-15T22:58:32Z)
* PR #19344 — meta lineCount sync (MERGED 2026-05-16T01:08:47Z)
* PR #18997 — STATE-SYNC iter 25 retcon (CLOSED, superseded by this S27)
* PR #17552 — iter 18 stale stack (CLOSED, superseded by iter 24a/25/26a)
* PR #17602 — iter 19 stale stack (OPEN, CONFLICTING; doctor/mechanic
  hygiene target, NOT this S27's responsibility)
* `proofs/Proofs/Hilbert10OQ01OQ02.lean` at SHA `8a3cda556b6`:
    * line 77: `import Mathlib.Algebra.Order.Ring.Basic` (post-#19137)
    * line 2657: Part VIII.31 (`sigma2_unionFinset_…`, iter 26a)
    * line 2727: Part VIII.32 (`pi2_intersectionFinset_…`, iter 26a)
    * line 3082: end of file (matches `meta.json.lineCount` after #19344)
