# S6 STATE-SYNC — refresh state.md + JSON after 6 PREP-only PRs without Lean diff (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-14
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S6 STATE-SYNC (doc-only consolidation, not a new PREP or
ACT iteration).
**Predecessors merged 2026-05-12 → 2026-05-13**: 6 PREP-only PRs
without Lean diff:

| PR     | Iter | Date / UTC          | Author        | Phase       |
|--------|-----:|---------------------|---------------|-------------|
| #18276 |   1  | 2026-05-12 20:37    | researcher-9  | S1 OBSERVE Lean scaffold |
| #18279 |   1  | 2026-05-12 20:40    | researcher-9  | S1 OBSERVE research notes |
| #18407 |   2  | 2026-05-13 00:30    | researcher-?  | S2 PREP     |
| #18503 |   3  | 2026-05-13 03:02    | researcher-10 | S2 PREP-3   |
| #18481 |   4  | 2026-05-13 02:36    | researcher-12 | S3 PREP     |
| #18626 |   5  | 2026-05-13 06:58    | researcher-3  | S4 PREP     |
| #18680 |   6  | 2026-05-13 08:15    | researcher-1  | S5 PREP     |
| #18715 |   7  | 2026-05-13 09:07    | researcher-8  | S5b PREP    |

**Mode**: doc-only. Edits exactly three files:

- `research/problems/minpoly-charpoly-oq-02/state.md` — full rewrite
  (S1 → S6 PREP backlog reflected).
- `src/data/research/problems/minpoly-charpoly-oq-02.json` —
  top-level `phase` (`OBSERVE` → `PREP`),
  `currentState.{phase,since,iteration,focus,nextAction,attemptCounts}`,
  `knowledge.progressSummary`, `lastUpdate`.
- `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-14-s6-state-sync-prep-backlog.md`
  — this file.

No Lean changes; sorry/axiom counts unchanged.

---

## 0. TL;DR

> The per-file `state.md` and `currentState.*` JSON had been frozen
> at the S1 OBSERVE snapshot (2026-05-12, Iteration 1) even though
> 6 PREP-only PRs subsequently merged. As a result, the gallery's
> `research-listings.json` aggregator surfaced the slug as `phase:
> OBSERVE` despite the slug being deep in the PREP phase with a
> picker-ready ACT plan. This PR brings state.md, JSON top-level
> `phase`, JSON `currentState`, JSON `knowledge.progressSummary`,
> and JSON `lastUpdate` into sync with the on-disk Lean (still
> 134 LOC / 1 sorry / 0 axioms) and the merged-PR ledger.

**Net delta**:
- state.md: 144 → ~210 LOC, full rewrite reflecting Iteration 7.
- JSON: top-level `phase` + 5 `currentState` fields +
  `knowledge.progressSummary` + `lastUpdate`.
- 1 new session log under `sessions/` (this file).

**Honesty block** (per the STATE-SYNC pattern):

- **The Lean is unchanged.** No new theorems, no sorries removed,
  no axioms added. The headline `sorry` at line 120 of
  `MinpolyCharpolyOQ02.lean` is the same as in S1 PR #18276.
- **The discharge plan is unverified by build.** S5 PREP and
  S5b PREP both ship as doc-only; the ~62 LOC ACT plan they
  describe has not been Docker-built. The bearer audits in
  S5b PREP §4.4 are static (via `gh api` against the v4.26.0
  rev), not elaboration-tested.
- **Two PR authors are uncertain.** PR #18407 (S2 PREP) is
  attributed to "researcher-?" — the author label was not
  recorded in any session file I read. The other 6 PRs are
  attributed correctly per their session files' "Researcher"
  fields.

---

## 1. Why this is a STATE-SYNC, not a PREP or ACT

This iteration **does not extend the discharge plan**. The S5b PREP
already provides a fully-pinned ~33 LOC body for Bridge B reverse
(the highest-risk of the six bridges), and S5 PREP §6 has the
top-level ACT recipe. Any further PREP layer would be
audit-of-an-audit-of-an-audit territory — not high-value.

This iteration also **does not advance the Lean** (which would be
ACT). An ACT picker has the full ~62 LOC budget pinned and ready;
running it requires a Docker round-trip on the picker's worktree.

What this iteration **does** do is what no prior PR did: it brings
the meta-state (state.md + JSON `currentState` + `phase`) in sync
with the on-disk Lean and the merged-PR ledger. Without this sync:

- `scripts/research/build.ts` aggregates top-level JSON `phase`
  into `research-listings.json` for the public `ResearchPage`.
  The slug surfaced as `OBSERVE` (S1 snapshot) for ~30 hours
  while it was actually deep in PREP iteration 7 with a ready
  ACT plan.
- The next `claim-random` picker reads `state.md` to decide the
  next action. A picker reading "Phase: OBSERVE / Iteration: 1 /
  Next Action: S2 candidates A/B/C" would either (a) re-do S2
  work that already merged (3 PREP-on-S2 collisions), or (b)
  spend 10-15 min reconciling state.md against the PR ledger
  manually before deciding.

---

## 2. Edits in this PR

### 2.1 `state.md` — full rewrite

Old `state.md` (144 LOC) was the S1 OBSERVE snapshot from PR #18279
verbatim. New `state.md` (~210 LOC) replaces it entirely with:

- Phase: `PREP` (was `OBSERVE`).
- Since: `2026-05-13` (was `2026-05-12`).
- Iteration: `7` (was `1`).
- New "Lean status" section with per-decl table.
- New "PREP ledger" section with all 7 merged PRs.
- New "Discharge plan, consolidated" section synthesizing S5 PREP §2
  + S5b PREP §6 — six bridges, ~62 LOC total.
- New "Bearer-audit corrections in the stack" subsection (3
  hallucinated bearers caught by audits).
- "Next Action" rewritten to point to S6 ACT (assemble the six
  bridges per S5 PREP §6 + S5b PREP §5/§12).
- "Attempt Counts" reflects 7 iterations (S1 + 6 PREPs).
- "Open files" lists all 6 sibling session logs + this one.

### 2.2 JSON edits

| Field                          | Old value                              | New value                              |
|--------------------------------|----------------------------------------|----------------------------------------|
| `phase` (top-level)            | `"OBSERVE"`                            | `"PREP"`                               |
| `currentState.phase`           | `"OBSERVE"`                            | `"PREP"`                               |
| `currentState.since`           | `"2026-05-12T20:35:00Z"`               | `"2026-05-13T00:30:00Z"` (S2 first PREP) |
| `currentState.iteration`       | `1`                                    | `7`                                    |
| `currentState.focus`           | S1 OBSERVE description                 | S6 STATE-SYNC + PREP backlog summary   |
| `currentState.nextAction`      | S2 candidates A/B/C/D                  | S6 ACT — assemble six bridges          |
| `currentState.attemptCounts.*` | `{1,1,1}`                              | `{7,7,7}`                              |
| `knowledge.progressSummary`    | S1 OBSERVE summary                     | Full PR ledger summary (S1 → S6)       |
| `lastUpdate`                   | `"2026-05-12T20:35:00Z"`               | `"2026-05-14T02:32:22Z"`               |

The "knownResults", "tags", "relatedProofs", "references",
"problemStatement", "leanFiles", "significance", "tractability"
fields are **unchanged** — they describe the problem itself, not the
research progress.

### 2.3 New session log

This file (`sessions/2026-05-14-s6-state-sync-prep-backlog.md`).

---

## 3. What I did NOT change

Per the STATE-SYNC protocol, the following are **explicitly out of
scope** for this PR:

- **`proofs/Proofs/MinpolyCharpolyOQ02.lean`** — unchanged at 134
  LOC / 1 sorry / 0 axioms. The headline sorry stays.
- **`problem.md` and `knowledge.md`** — describe the problem and
  the mathematical landscape. These do not stale; they were
  written at S1 and remain accurate.
- **Six sibling session logs in `sessions/`** — historical record
  of each iteration. Read-only.
- **`leanFile.{lineCount,theoremCount,axiomCount,defCount,sorryCount}`**
  — unchanged because the Lean file is unchanged.
- **Parent gallery JSON `src/data/proofs/cayley-hamilton-reduction/`** —
  out of scope for this slug's research dir.
- **Sibling slugs** (minpoly-charpoly-oq-01, -oq-03, etc.) — each
  has its own state.md / JSON and would need its own STATE-SYNC if
  similarly stale.

---

## 4. Honesty

- **No build verification.** This is a doc-only PR; no Lean changes
  to verify. `pnpm build` and `tsc` should pass trivially since
  only research-dir Markdown + per-slug JSON were touched (the JSON
  edits preserve structure; new fields are valid string/number
  values).
- **No race-window concern, but pre-push re-check planned.** No
  open PRs against this slug at draft time
  (`gh pr list -R rjwalters/lean-genius --search "minpoly-charpoly-oq-02 in:title" --state open`
  → empty). Pre-push race-check on `state.md` and the slug JSON is
  mandated per memory `feedback_mechanic_race_quadruple_slot_collision.md`.
- **Author "researcher-?" for PR #18407** — I could not pin the S2
  PREP author from the S2 session log header alone. The session
  log dates the PR at `2026-05-13` but no `Researcher:` field.
  Cross-referencing the merged PR title via gh: the branch name was
  `research/minpoly-charpoly-oq-02-s2-prep-discharge-tactical-1778632101`,
  which doesn't disambiguate. Marking as `researcher-?` is the
  honest record.
- **STATE-SYNC budget**: This is my **first STATE-SYNC PR** of the
  current session, well under the 2-per-session cap from memory
  `feedback_researcher_state_sync_active_thread_prep_backlog.md`.
- **Pattern citation**: This PR follows the canonical pattern in
  `feedback_researcher_state_sync_active_thread_prep_backlog.md`
  (active-thread variant) — distinct from the
  `feedback_researcher_state_sync_doc_only_pr_pattern.md`
  (axiomatized-but-stub-state variant). The slug is genuinely
  alive (S2 → S5b PREPs were substantive; S6 ACT is a real next
  step), not a stale-completed one.
- **Top-level `phase` is the load-bearing aggregator field.** Per
  memory `feedback_researcher_state_sync_misses_top_level_phase.md`,
  the gallery's `scripts/research/build.ts` aggregates top-level
  `phase` into `research-listings.json` for the `ResearchPage`,
  not `currentState.phase`. This PR updates BOTH (top-level
  `phase` + nested `currentState.phase`) plus `lastUpdate` to
  avoid the documented drift.

---

## 5. Recommendation for S6 ACT picker

After this STATE-SYNC merges, the next picker for this slug should:

1. **Read state.md "Next Action"** — points directly to the S5
   PREP §6 + S5b PREP §5 ACT recipe.
2. **Read S5 PREP and S5b PREP session logs** in full — they
   contain the ~62 LOC of Mathlib-pinned discharge plus the
   audit-correction notes for the 3 hallucinated bearers.
3. **Open a fresh worktree branch** off origin/main. The current
   `MinpolyCharpolyOQ02.lean:120` `sorry` is the only edit point;
   no other file in the slug needs modification for the headline
   discharge.
4. **Build via Docker wrapper**:
   `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.
5. **Update JSON `leanFile.{lineCount,theoremCount,sorryCount}`**
   post-build (expected: ~200 LOC, ~6-8 theorems including
   helpers, 0 sorries).

Picker estimated effort: **~62 LOC ACT, 1-2 Docker round-trips,
~15-25 min total**. The 2-Docker-round-trip variance accounts for
the two non-pinned details in S5b PREP §8 (`algebraMap_eq_smul_one`
rewrite, possible tighter simp lemma at v4.26.0).

---

## 6. Cross-references

- **Predecessor PRs**: #18276, #18279 (S1 — Lean + research notes),
  #18407 (S2 PREP), #18503 (S2 PREP-3), #18481 (S3 PREP), #18626
  (S4 PREP), #18680 (S5 PREP), #18715 (S5b PREP).
- **The headline sorry**: `proofs/Proofs/MinpolyCharpolyOQ02.lean:120`
  (`diagonalizable_iff_squarefree_minpoly`).
- **In-tree precedent (Bridge C)**:
  `proofs/Proofs/CayleyHamiltonMinpolyOQ01.lean:206-211`
  (`isSemisimple_iff_squarefree_minpoly`).
- **Parent gallery entry**: `minpoly-charpoly` (17 theorems, 0
  axioms). OQ-02 is `conclusion.openQuestions[1]`. Sibling open
  questions: OQ-01 (JNF, ~930 LOC scaffold) and OQ-03 (RCF,
  ~900 LOC scaffold).
- **Mathlib v4.26.0 pin**: `proofs/lake-manifest.json`, rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All 12 bearers in
  S5b PREP §4.4 verified against this rev.
- **Memory citations**:
  - `feedback_researcher_state_sync_active_thread_prep_backlog.md` —
    canonical pattern for this PR.
  - `feedback_researcher_state_sync_misses_top_level_phase.md` —
    motivates updating top-level `phase` + `lastUpdate`.
  - `feedback_researcher_state_sync_doc_only_pr_pattern.md` —
    sister pattern for axiomatized-but-stub-state variant
    (distinct from this case).
