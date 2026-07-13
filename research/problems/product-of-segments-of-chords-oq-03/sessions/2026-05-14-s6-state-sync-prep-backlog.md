# S6 STATE-SYNC — refresh state.md + JSON after 3 PREP-only PRs without Lean diff (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-14
**Slug**: `product-of-segments-of-chords-oq-03`
**Phase**: S6 STATE-SYNC (doc-only consolidation, not a new PREP or
ACT iteration).
**Predecessors merged 2026-05-13**: 3 PREP-only PRs without Lean diff:

| PR     | Iter | Date / UTC          | Author        | Phase                                                              |
|--------|-----:|---------------------|---------------|--------------------------------------------------------------------|
| #18231 |   1  | 2026-05-12 18:17    | researcher-11 | S1 OBSERVE                                                         |
| #18380 |   2  | 2026-05-12 23:43    | researcher-3  | S2 SCAFFOLD (build pending; only Lean iteration)                   |
| #18466 |   3  | 2026-05-13 02:19    | researcher-9  | S3 PREP — Cramer (⇐) discharge design                              |
| #18474 |   4  | 2026-05-13 02:30    | researcher-12 | S4 PREP — concyclic → Δ = 0 row reduction design                   |
| #18553 |   5  | 2026-05-13 03:50    | researcher-5  | S5 PREP — chord-product → Δ = 0 bridge strategy                    |

**Mode**: doc-only. Edits exactly three files:

- `research/problems/product-of-segments-of-chords-oq-03/state.md` —
  full rewrite (S1 → S6 PREP backlog reflected).
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` —
  top-level `phase` (`OBSERVE` → `PREP`),
  `currentState.{phase,since,iteration,focus,nextAction,attemptCounts}`,
  `knowledge.progressSummary`, `lastUpdatedAt`.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-14-s6-state-sync-prep-backlog.md`
  — this file.

No Lean changes; sorry/axiom counts unchanged at 1/0.

---

## 0. TL;DR

> The per-file `state.md` and `currentState.*` JSON had been frozen
> at the S2 SCAFFOLD snapshot (2026-05-12, Phase: ACT, Iteration: 2,
> Next: S3) even though 3 PREP-only PRs subsequently merged. As a
> result, the gallery's `research-listings.json` aggregator surfaced
> the slug as `phase: OBSERVE` (the JSON `phase` field hadn't even
> caught up to S2's ACT label). This PR brings state.md, JSON
> top-level `phase`, JSON `currentState`, JSON
> `knowledge.progressSummary`, and JSON `lastUpdatedAt` into sync
> with the on-disk Lean (still 106 LOC / 1 sorry / 0 axioms in
> `Proofs/ProductOfSegmentsOfChordsOQ03.lean`) and the merged-PR
> ledger.

**Net delta**:
- state.md: 102 → ~210 LOC, full rewrite reflecting Iteration 5.
- JSON: top-level `phase` + 6 `currentState` fields +
  `knowledge.progressSummary` + `lastUpdatedAt`.
- 1 new session log under `sessions/` (this file).

**Honesty block**:

- **The Lean is unchanged.** No new theorems, no sorries removed,
  no axioms added. The headline `sorry` at line ~106 of
  `ProductOfSegmentsOfChordsOQ03.lean` is the same as in S2 PR #18380.
- **Build status remains "pending".** S2 SCAFFOLD was labelled
  build-pending (the S2 author hit a `proofs/.lake` self-symlink
  loop in the worktree); none of S3/S4/S5 PREPs forced a rebuild.
  The S6 ACT picker should Docker-build BEFORE patching to
  establish baseline.
- **The discharge plan is unverified by build.** S3, S4, and S5
  PREPs all ship as doc-only; the ~170 LOC ACT plan they describe
  has not been Docker-built. The bearer audits in S3 PREP §4 are
  partially gated by the S3 author's "rate-limit-blocked
  verification queue" caveat.
- **JSON schema variation**: this slug uses `lastUpdatedAt` and
  `createdAt` (with sub-second `0.000Z`), distinct from the
  `lastUpdate`/`started` schema used in some other slug JSONs
  (e.g., minpoly-charpoly-oq-02). I preserved the existing schema
  rather than introducing a normalization edit (per memory
  `feedback_researcher_state_sync_misses_top_level_phase.md` —
  schema normalization is enrich-research.ts scope, not researcher).

---

## 1. Why this is a STATE-SYNC, not a PREP or ACT

This iteration **does not extend the discharge plan**. The 3 PREPs
already cover all three discharge sub-tasks (Cramer for (⇐), row
reduction for (⇒), chord-product bridge), and S6 ACT is a real
ready-to-go next step.

This iteration also **does not advance the Lean** (which would be
ACT). An ACT picker has the full ~170 LOC budget pinned and ready;
running it requires a Docker round-trip on the picker's worktree.

What this iteration **does** do is what no prior PR did: it brings
the meta-state in sync. Without this sync:

- `scripts/research/build.ts` aggregates top-level JSON `phase`
  into `research-listings.json` for the public `ResearchPage`.
  The slug surfaced as `OBSERVE` for ~33+ hours while it was
  actually deep in PREP iteration 5 with a 3-PREP-deep ACT plan.
- The next `claim-random` picker reads `state.md` to decide the
  next action. A picker reading "Phase: ACT / Iteration: 2 /
  Next Action: S3 ..." would either (a) re-do S3 work (PR #18466
  already merged), or (b) waste 10-15 min reconciling state.md
  against the PR ledger manually before deciding.

---

## 2. Edits in this PR

### 2.1 `state.md` — full rewrite

Old `state.md` (102 LOC) was the S2-era snapshot. New `state.md`
(~210 LOC) replaces it entirely with:

- Phase: `PREP` (was `ACT`).
- Since: `2026-05-13T02:19:00Z` (was `2026-05-12T23:39:00Z`).
- Iteration: `5` (was `2`).
- New "Lean status" section with per-decl table.
- New "PREP ledger" section with all 5 merged PRs.
- New "Discharge plan, consolidated" section synthesizing S3 + S4 +
  S5 PREP — three concrete ACT iterations + parent axiom discharge.
- New "S3 PREP key decisions" / "S4 PREP key decision" / "S5 PREP
  key chain" sub-sections.
- "Next Action" rewritten to point to S6 ACT (assemble S3/S4/S5/S6
  ACT iterations into sequential or single-PR discharge).
- "Attempt Counts" reflects 5 iterations (S1, S2, S3, S4, S5).
- "Open files" lists all 3 sibling session logs + this one.
- "Subsequent Plan" table preserved + S3-S6 ACT entries marked
  pending.
- New "Blockers" entry: build-pending precaution per
  `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`
  (4 consecutive build-pending/doc-only PRs in a row).

### 2.2 JSON edits

| Field                          | Old value                              | New value                              |
|--------------------------------|----------------------------------------|----------------------------------------|
| `phase` (top-level)            | `"OBSERVE"`                            | `"PREP"`                               |
| `currentState.phase`           | `"OBSERVE"`                            | `"PREP"`                               |
| `currentState.since`           | `"2026-05-12T18:00:00.000Z"`           | `"2026-05-13T02:19:00.000Z"` (S3 first PREP) |
| `currentState.iteration`       | `1`                                    | `5`                                    |
| `currentState.focus`           | S1 OBSERVE description                 | S6 STATE-SYNC + PREP backlog summary   |
| `currentState.nextAction`      | "S2: create ..."                       | S6 ACT — assemble S3/S4/S5/S6 ACT iterations |
| `currentState.attemptCounts.*` | `{1,1,1}`                              | `{5,5,5}`                              |
| `knowledge.progressSummary`    | S1 OBSERVE summary                     | Full PR ledger summary (S1 → S6)       |
| `lastUpdatedAt`                | `"2026-05-12T18:30:00Z"`               | `"2026-05-14T02:42:00Z"`               |

The `knownResults`, `tags`, `relatedGalleryProofs`,
`problemStatement`, `significance`, `tractability`, `createdAt`,
`knowledge.{builtItems,insights,mathlibGaps,nextSteps}` fields are
**unchanged** — they describe the problem itself, not the research
progress.

### 2.3 New session log

This file (`sessions/2026-05-14-s6-state-sync-prep-backlog.md`).

---

## 3. What I did NOT change

Per the STATE-SYNC protocol, the following are **explicitly out of
scope** for this PR:

- **`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean`** — unchanged
  at 106 LOC / 1 sorry / 0 axioms. The headline sorry stays.
- **`proofs/Proofs/ProductOfSegmentsOfChords.lean`** — parent file;
  axiom `converse_product_implies_concyclic_axiom` at line 468 is
  the eventual S6 ACT discharge target, but unchanged in this PR.
- **`problem.md` and `knowledge.md`** — describe the problem and
  the mathematical landscape. These do not stale; they were
  written at S1 and remain accurate.
- **3 sibling session logs in `sessions/`** — historical record of
  each PREP iteration. Read-only.
- **Parent gallery JSON `src/data/proofs/product-of-segments-of-chords/`** —
  out of scope for this slug's research dir.
- **JSON `knowledge.{builtItems,insights,mathlibGaps,nextSteps}`** —
  these reflect S1 OBSERVE's mathematical analysis and remain
  accurate; refreshing them would be enricher scope.
- **Gallery `meta.json` `axiomCount`** — currently 1; will drop to
  0 only when S6 ACT actually discharges the axiom.

---

## 4. Honesty

- **No build verification.** This is a doc-only PR; no Lean changes
  to verify. `pnpm build` and `tsc` should pass trivially since
  only research-dir Markdown + per-slug JSON were touched (the JSON
  edits preserve structure and field types).
- **No race-window concern.** No open PRs against this slug at
  draft time
  (`gh pr list -R rjwalters/lean-genius --search "product-of-segments-of-chords-oq-03 in:title" --state open`
  → empty). Pre-push race-check on `state.md` and the slug JSON is
  mandated.
- **STATE-SYNC budget**: This is my **second STATE-SYNC PR** of the
  current session, **at the 2-per-session cap** from memory
  `feedback_researcher_state_sync_active_thread_prep_backlog.md`.
  The first was `minpoly-charpoly-oq-02` PR #18976 (~2 hours
  earlier).
- **Pattern citation**: Same canonical pattern as PR #18976 —
  active-thread variant with PREP backlog. Distinct from
  stale-completed STATE-SYNC and from the canonical/misplaced-path
  variant in PR #18961 (sperner-simplicial-instance-oq-05).
- **Top-level `phase` is the load-bearing aggregator field.** Per
  memory `feedback_researcher_state_sync_misses_top_level_phase.md`,
  the gallery's `scripts/research/build.ts` aggregates top-level
  `phase` into `research-listings.json` for the `ResearchPage`,
  not `currentState.phase`. This PR updates BOTH (top-level
  `phase` + nested `currentState.phase`) plus `lastUpdatedAt` to
  avoid the documented drift.
- **Build-pending caveat preserved.** state.md prior version
  flagged S2 SCAFFOLD as build-pending; I preserve this in the
  refreshed state.md "Blockers" section and add a Memory citation
  to `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`
  warning the S6 ACT picker that 4 consecutive
  build-pending/doc-only PRs in a row should trigger a
  Docker-build-baseline check BEFORE patching.

---

## 5. Recommendation for S6 ACT picker

After this STATE-SYNC merges, the next picker for this slug should:

1. **Read state.md "Next Action"** — points directly to the S3 +
   S4 + S5 PREP ACT recipes.
2. **Docker-build the existing S2 file** to establish baseline:
   `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`.
   If the build fails on origin/main, ship a "build unblocker"
   PR per memory
   `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`
   first.
3. **Read S3, S4, S5 PREP session logs** in full — they contain
   the ~170 LOC of designed discharge plus the friction-point map
   (Vec2 ↔ Fin 2 → ℝ, ‖·‖ on EuclideanSpace, Real.sqrt
   positivity).
4. **Open a fresh worktree branch** off origin/main. The current
   `ProductOfSegmentsOfChordsOQ03.lean:106` `sorry` is the only
   edit point for S3-S5 ACT; S6 ACT additionally edits parent
   `ProductOfSegmentsOfChords.lean:468` + parent gallery
   `meta.json`.
5. **Update JSON `currentState`** post-build (focus/nextAction;
   `iteration` increments; `phase` flips to ACT or VERIFIED).
6. **Update parent gallery `meta.json`**: `axiomCount` 1 → 0;
   `status` toward `"verified"` if all sorries close.

Picker estimated effort: **~170 LOC ACT, 2-4 Docker round-trips,
~45-90 min total** depending on whether S3/S4/S5/S6 are split
across PRs or bundled.

---

## 6. Cross-references

- **Predecessor PRs**: #18231 (S1 OBSERVE), #18380 (S2 SCAFFOLD),
  #18466 (S3 PREP), #18474 (S4 PREP), #18553 (S5 PREP).
- **The headline sorry**:
  `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:106`
  (`concyclicityDet_eq_zero_iff_concyclic`).
- **The eventual S6 ACT discharge target**:
  `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
  (`converse_product_implies_concyclic_axiom`).
- **Parent gallery entry**: `product-of-segments-of-chords`. OQ-03
  is `meta.json:conclusion.openQuestions[2]`.
- **Companion STATE-SYNC PR this session**: PR #18976
  (`minpoly-charpoly-oq-02`, S6 STATE-SYNC, similar 6-PREP-stack
  pattern). Both follow the same active-thread-PREP-backlog
  template.
- **Memory citations**:
  - `feedback_researcher_state_sync_active_thread_prep_backlog.md` —
    canonical pattern for this PR.
  - `feedback_researcher_state_sync_misses_top_level_phase.md` —
    motivates updating top-level `phase` + `lastUpdatedAt`
    (preserving the slug's existing schema casing).
  - `feedback_researcher_build_pending_slug_series_silent_parent_regression.md` —
    motivates the S6 ACT picker's Docker-build-baseline
    precaution (4 consecutive doc-only/build-pending PRs).
  - `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md` —
    fallback if Docker baseline reveals pre-existing
    parent-file regression.
