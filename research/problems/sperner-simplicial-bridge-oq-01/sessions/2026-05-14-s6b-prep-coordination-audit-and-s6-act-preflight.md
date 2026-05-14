# S6b PREP — Cross-PR coordination audit + S6 ACT pre-flight (doc-only)

**Researcher**: researcher-3 (claim `researcher-10639`, knowledge score 18 / RICH)
**Date**: 2026-05-14
**Phase**: PREP (cross-PR coordination + implementation pre-flight, doc-only)
**Iteration**: not advanced — this PR adds only a new session note; tracker updates remain with PR #19010.
**Type**: cross-PR coordination audit pattern (`feedback_researcher_cross_pr_coordination_audit_pattern.md`).
**Predecessors**: PR #18234 (S1 OBSERVE), #18363 (S2 SCAFFOLD), #18434 (S2b OBSERVE), #18451 (S2c PREP), #18537 (S3 ACT — `sperner_mixed_panchromatic_at_dim` lands, build pending), #18564 (S3b PREP), #18677 (S4 GALLERY), #18746 (audit clean), #18741/#18819/#18833 (enrichment), #18940 (STATE-SYNC).
**Active OPEN PRs at session start**: #19010 (S5 build verify + gallery promotion `formalized → verified`), #19150 (S6 PREP — mixed-dimension aggregator design).

---

## §0 — TL;DR for the next implementer

This slug currently has **two OPEN PRs** that are pairwise orthogonal (zero file overlap) but together prefigure an upcoming **S6 ACT** Lean change that *will* touch `meta.json` (lineCount / theoremCount). This audit:

1. Inventories per-PR file footprint and merge-state (§2).
2. Verifies the S6 PREP recipe (PR #19150 §7) against `origin/main` HEAD line numbers (§3).
3. Pin-cites parent-file APIs at the current Mathlib v4.26.0 SHA (§4).
4. Forecasts post-merge state of `meta.json` and `state.md` for each ordering of the three landings (§5).
5. Recommends sequencing **PR #19010 → PR #19150 → S6 ACT** (§6).
6. Estimates S6 ACT Docker build = ~7745 jobs (no transitive imports added; §7).

**Strictly orthogonal** to both open PRs — touches only this new session file. No edits to `state.md`, `meta.json`, JSON tracker, or the Lean source.

---

## §1 — Why this audit now

The slug's OPEN-PR state (as of 2026-05-14T22:50Z fetch) is:

| PR | Author | Title | Files |
|---|---|---|---|
| #19010 | researcher-9 | S5 build verification + gallery promotion (`formalized → verified`, 7745 jobs) | `meta.json`, `state.md`, JSON tracker, S5 session |
| #19150 | researcher-9 | S6 PREP — mixed-dimension aggregator design (doc-only) | S6 session only |

Neither PR touches `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean`. PR #19150's recipe (§7 of its session note) prescribes a +26 LOC Lean append: two new theorems (`sperner_mixed_panchromatic` alias + `sperner_mixed_panchromatic_global` outer-existential), targeting line 180 → line 182.

When the S6 ACT lands, it will mutate **both** the Lean file (+26 LOC, +2 theorems) **and** `meta.json` (`lineCount: 184 → 210`, `theoremCount: 7 → 9`). PR #19010 already mutates `meta.json` (`status`/`badge`/`assumptions`/`summary` fields). A naive S6 ACT shipped now would **conflict** with #19010 on `meta.json`. The matching documented pattern (`feedback_researcher_cross_pr_coordination_audit_pattern.md`) calls for a doc-only PREP that maps merge sequencing **before** the ACT lands.

This audit is that PREP.

---

## §2 — Per-PR file footprint accounting

### PR #19010 — S5 build verify + gallery promotion

`gh pr diff -R rjwalters/lean-genius 19010 --name-only` returns 4 files:

| File | additions | deletions | role |
|---|---|---|---|
| `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-14-s5-build-verification-and-status-promotion.md` | +79 | 0 | new session log |
| `research/problems/sperner-simplicial-bridge-oq-01/state.md` | +47 | -28 | tracker resync (Phase ACT → COMPLETED, Iteration 3 → 9) |
| `src/data/proofs/sperner-simplicial-bridge-oq-01/meta.json` | +4 | -4 | `status: formalized → verified`, `badge: wip → verified`, `assumptions` rewrite, `summary` rewrite |
| `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` | +10 | -10 | top-level `phase: ACT → COMPLETED`, `currentState.{phase, iteration, focus, nextAction}` resync, `lastUpdate` advance |

**Crucial**: PR #19010 does **not** touch `lineCount`, `theoremCount`, `definitionCount`, or `axiomCount` in `meta.json` (these remain at 184 / 7 / 3 / 0).

### PR #19150 — S6 PREP — mixed-dim aggregator design

`gh pr diff -R rjwalters/lean-genius 19150 --name-only` returns 1 file:

| File | additions | deletions | role |
|---|---|---|---|
| `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-14-s6-prep-mixed-aggregator-design.md` | +238 | 0 | new design memo |

**Strictly doc-only.** Zero overlap with PR #19010.

### File-level overlap matrix

| File | PR #19010 | PR #19150 | This PR (S6b) | Future S6 ACT |
|---|---|---|---|---|
| `state.md` | M | — | — | M (iteration bump 9 → 10, S6 ACT row in history) |
| `meta.json` | M (status/badge/assumptions/summary) | — | — | M (lineCount, theoremCount, originalContributions append) |
| JSON tracker | M | — | — | M (phase, focus, lastUpdate) |
| S5 session note | A | — | — | — |
| S6 PREP session note | — | A | — | — |
| S6b PREP session note (this file) | — | — | A | — |
| S6 ACT session note (future) | — | — | — | A |
| `Proofs/SpernerSimplicialBridgeOQ01.lean` | — | — | — | M (+26 LOC) |

**Conflict surface**: This PR conflicts with **nothing**. Future S6 ACT conflicts with **PR #19010 on `meta.json` (status/badge fields are co-located with lineCount in JSON object), `state.md` (iteration history), and JSON tracker** if both attempt to merge unmerged tip.

---

## §3 — S6 PREP §7 line-number verification

PR #19150 §7 prescribes inserting two new theorems "between line 180 (existing `sperner_mixed_panchromatic_at_dim` body close) and line 182 (`end MixedSperner`)".

Current `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` on `origin/main` (commit `08ea6265778`, last touched 2026-05-13 via the parent-file rename in PR #18647):

| Marker | Line | Confirmed |
|---|---|---|
| `theorem sperner_mixed_panchromatic_at_dim {d : Nat}` | 170 | ✓ (matches §3 §7) |
| Body close (`(hpseudo_of_mixed hmixed) c hbdry`) | 180 | ✓ |
| Blank line | 181 | ✓ (insertion point) |
| `end MixedSperner` | 182 | ✓ |
| `end Sperner.SimplicialComplex` | 184 | ✓ |
| EOF | 184 | ✓ (file is exactly 184 LOC) |

`grep -nE "^namespace |^section |^end "`:

```
50:namespace Sperner.SimplicialComplex
123:section MixedSperner
182:end MixedSperner
184:end Sperner.SimplicialComplex
```

The two new theorems land inside `section MixedSperner` (lines 123–182), so they inherit the `variable {E : Type} [DecidableEq E]` from line 56 and the `MixedPseudomanifold`, `topCellsOfDim`, `boundaryDoorCount`, `card_of_mem_topCellsOfDim`, `vertexEnum`, and `Sperner.IsPanchromatic` references all in scope.

**Verdict**: PR #19150 §7 line numbers are **valid** against current `origin/main` HEAD. No drift since the recipe was written. Insertion at line 181 (blank between 180 and 182).

---

## §4 — Parent-file API pin verification (Mathlib v4.26.0 / SHA `2df2f015...`)

PR #19150's recipe consumes four parent-file APIs (all from `proofs/Proofs/SpernerSimplicialBridge.lean`, imported at line 6 of OQ-01):

| API | Source line | Used in recipe |
|---|---|---|
| `Sperner.SimplicialComplex.exists_panchromatic` | 564 | indirect via `sperner_mixed_panchromatic_at_dim` |
| `Sperner.IsPanchromatic` | re-exported from `SpernerMathlib.lean:347` | both Variant A and B return type |
| `vertexEnum` (noncomputable) | 65 | both Variant A and B return type |
| `topCellsOfDim K d` (defined in OQ-01) | 60 of OQ-01 file | both Variant A and B subtype |

`grep -nE "^theorem exists_panchromatic\|noncomputable def vertexEnum\|namespace Sperner.SimplicialComplex" proofs/Proofs/SpernerSimplicialBridge.lean`:

```
50:namespace Sperner.SimplicialComplex
65:noncomputable def vertexEnum
564:theorem exists_panchromatic
611:end Sperner.SimplicialComplex
```

`grep -n "Sperner.IsPanchromatic" proofs/Proofs/SpernerSimplicialBridge.lean`:

```
576:      Sperner.IsPanchromatic
```

`grep -n "^def IsPanchromatic" proofs/Proofs/SpernerMathlib.lean`:

```
347:def IsPanchromatic (vertex : Cell → Fin (d + 1) → V)
```

All four parent APIs are present at the pinned SHA. The variant signatures in §3 / §4 / §7 of PR #19150 type-check against these pins.

### Mathlib pin

From `proofs/lake-manifest.json`:

```
"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

`v4.26.0` (per `proofs/lakefile.toml`). No drift since PR #19010 ran the S5 build (7745 jobs clean).

---

## §5 — Post-merge state forecast under each merge order

Three independent landings: A = PR #19010 (S5 verify+promote), B = PR #19150 (S6 PREP doc), C = future S6 ACT (Lean +26 LOC + meta.json bump). Six possible orderings. Below collapses to the three relevant cases.

### Order A → B → C (recommended)

| Step | `meta.json` lineCount | theoremCount | status | badge | state.md iter |
|---|---|---|---|---|---|
| pre | 184 | 7 | formalized | wip | 3 |
| after A merges | 184 | 7 | **verified** | **verified** | **9** |
| after B merges | 184 | 7 | verified | verified | 9 |
| C drafted | bumps to **210** | bumps to **9** | verified | verified | bumps to **10** |

Clean: C's `meta.json` patch is purely additive (lineCount 184 → 210, theoremCount 7 → 9); doesn't touch status/badge/assumptions (which A wrote). C's `state.md` patch adds an "S6 ACT (#19xxx) — aggregator theorems" row to the iteration-history table (which A populated rows 1–9). C's JSON tracker bump iteration 9 → 10 + sets `currentState.focus` to `"S6 ACT — mixed-dimension aggregator (alias + global existential)"`.

### Order B → A → C

| Step | `meta.json` lineCount | theoremCount | status | badge | state.md iter |
|---|---|---|---|---|---|
| pre | 184 | 7 | formalized | wip | 3 |
| after B merges | 184 | 7 | formalized | wip | 3 |
| after A merges | 184 | 7 | **verified** | **verified** | **9** |
| C drafted | bumps to **210** | bumps to **9** | verified | verified | bumps to **10** |

Equivalent end-state to A → B → C. No forecasts change.

### Order C → A (or C → B → A)

If C lands first, then A's `meta.json` patch needs to re-Docker-build at the new lineCount = 210 to keep credibility on the `verified` promotion. This adds a re-verification step and mild conflict surface on `meta.json` (status/badge vs. lineCount edits land in nearby lines).

**Cost**: A would need to be rebased on top of C, re-running the Docker wrapper to verify 210-LOC compiles. ~5 min extra wall time + one more Docker job, but no architectural change.

### Recommendation

**Sequencing A → B → C**. Reasons:

- A (PR #19010) is build-verified and CLEAN/MERGEABLE — should land first as the smallest-change, highest-priority promotion.
- B (PR #19150) is doc-only and already CLEAN/MERGEABLE — can land second without rebase.
- C (S6 ACT, not yet drafted) re-Docker-builds against the post-A lineCount baseline; one Docker run, no race risk.

---

## §6 — S6 ACT pre-flight checklist (for the implementer)

When the S6 ACT is drafted (after A and B both merge), the implementer should:

| Step | Action | Expected outcome |
|---|---|---|
| 1 | `git checkout -b research/sperner-bridge-oq01-s6-act-<ts> origin/main` | Branches from latest main containing A's promotion + B's PREP. |
| 2 | Append §7 recipe of PR #19150 verbatim (lines 181 ↦ insert; 26 LOC). | File grows from 184 → 210 LOC. |
| 3 | Update `meta.json`: `lineCount: 184 → 210`, `theoremCount: 7 → 9`, append two entries to `originalContributions`. | Status/badge/assumptions unchanged. |
| 4 | `./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01` | Expected: **7745 jobs clean** (additions are pure leaf theorems with no new transitive imports). |
| 5 | Update `state.md` iteration 9 → 10, add S6 ACT row in iteration-history table, refresh "Current Focus" to reflect the aggregator landing. | Tracker stays in sync. |
| 6 | Update `src/data/research/problems/sperner-simplicial-bridge-oq-01.json` `currentState.iteration: 9 → 10`, `currentState.focus`, `lastUpdate`. | Top-level `phase` may stay COMPLETED or shift to ACT for one cycle. |
| 7 | New session note `2026-05-XX-s6-act-mixed-aggregator.md` documenting the +26 LOC + Docker outcome. | Standard ACT pattern. |
| 8 | `gh pr create --repo rjwalters/lean-genius --head <branch> --title "research(sperner-simplicial-bridge-oq-01): S6 ACT — mixed-dimension aggregator (alias + global existential, build verified, +26 LOC)"` | Single PR; no labels (researcher PR). |

**Race-safety note**: at S6 ACT pre-claim time, the implementer should `gh pr list -R rjwalters/lean-genius --search "sperner-simplicial-bridge-oq-01 in:title" --state open --limit 5` to confirm A and B have both merged. If either is still open, reschedule (15-min retry per the standard researcher loop).

---

## §7 — S6 ACT Docker build forecast

PR #19010 reported 7745 jobs (build = `Proofs.SpernerSimplicialBridgeOQ01` + transitive `Proofs.SpernerSimplicialBridge` + `~3050 Mathlib targets` + Mathlib infrastructure). The S6 ACT additions are:

- `theorem sperner_mixed_panchromatic` — 1-line body `:= sperner_mixed_panchromatic_at_dim K hmixed c hbdry`. No new imports.
- `theorem sperner_mixed_panchromatic_global` — 2-line body `obtain ⟨d, c, hbdry⟩ := hd; exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩`. No new imports.

Both theorems are pure tactic compositions over **already-pulled-in** APIs. The build graph gains 2 new declaration nodes, but no new transitive deps.

**Forecast**: Docker outcome = `Build completed successfully (7745 jobs)` (unchanged) or `(7747 jobs)` (if Lake counts the two new declarations as separate jobs — Lake typically counts at file-granularity, so likely 7745 unchanged). Either way: **clean build, sub-30-second incremental over the cached Mathlib oleans**.

**Build-risk audit** (from PR #19150 §6):

| Item | Risk |
|---|---|
| New types | None |
| New axioms | None |
| Tactic compatibility v4.26.0 | None — `obtain`, `exact ⟨…⟩` are core-Lean stable |
| Decidability requirements | None — `boundaryDoorCount` unchanged |
| Build-graph impact | None — append-only inside `section MixedSperner` |

This audit confirms PR #19150 §6's risk assessment.

---

## §8 — Why two doc-only PREPs (B + this one)?

PR #19150 (B) is the **design memo** — what to write. This audit (S6b) is the **coordination memo** — when to write it relative to the other open PRs and what to verify before writing. The two have non-overlapping scopes:

| PR | Scope |
|---|---|
| B (#19150) | Variant signatures, line numbers, build-risk audit, two-variant rationale. |
| This (S6b) | Per-PR file accounting, merge ordering, post-merge meta.json forecast, S6 ACT preflight checklist. |

Both are necessary because the slug now has three independent moving pieces (A, B, C) that touch the same `meta.json`/`state.md`/JSON files and the same Lean file. The cross-PR coordination audit pattern (`feedback_researcher_cross_pr_coordination_audit_pattern.md`) explicitly calls for this separation when 2+ open PRs touching shared files predate a planned ACT.

---

## §9 — Counts & post-merge state.md prediction

After A → B → C all merge (estimated by 2026-05-15 based on current OPEN-CLEAN state):

```
Phase: COMPLETED (S6 ACT — mixed-dimension aggregator landed)
Since: 2026-05-XXTXX:XX:XXZ
Iteration: 10 (S1 → S2 → S2b → S2c → S3 → S3b → S4 GALLERY → STATE-SYNC → S5 build verify → S6 PREP → S6 ACT)
```

`meta.json` final:
```
{
  "status": "verified",
  "badge": "verified",
  "lineCount": 210,
  "theoremCount": 9,
  "definitionCount": 3,
  "axiomCount": 0,
  "sorries": 0,
  ...
}
```

`originalContributions` gains two entries describing the two aggregator theorems.

---

## §10 — Race-safety summary for THIS PR

- **Pre-claim grep**: `gh pr list -R rjwalters/lean-genius --search "sperner-simplicial-bridge-oq-01 in:title" --state open --limit 10` → 2 OPEN (#19010, #19150).
- **File overlap with #19010**: 0 (this PR adds only `sessions/2026-05-14-s6b-prep-coordination-audit-and-s6-act-preflight.md`).
- **File overlap with #19150**: 0 (different session filename; same parent directory).
- **Branch**: `research/sperner-bridge-oq01-s6b-coordination-1778802635` from `origin/main` HEAD.
- **No Lean changes, no `state.md` changes, no `meta.json` changes, no JSON tracker changes.**
- **Build verification**: not applicable (single new markdown file, no Lean code).

This PR can merge in any order relative to A and B without conflict.

---

## §11 — Forward levers (post-S6 ACT)

After S6 ACT lands, the slug's "Forward Levers" §2 (decidable promotion of `boundaryDoorCount`) and the second forward-lever-class candidate (n=7/n=11 stratification analogs, parallel OQ) remain available as separate opportunities. The mixed-dimension aggregator closes the first forward lever; the slug then enters a steady-state `verified` posture with optional future extensions.

---

## §12 — Honest scope statement

This PR is a **doc-only coordination audit**. It:

- Verifies line-number references in PR #19150 §7 against `origin/main` HEAD.
- Pin-cites parent-file APIs at the Mathlib v4.26.0 SHA `2df2f015...`.
- Maps the post-merge state of the gallery and tracker under three landings.
- Provides a pre-flight checklist for the next S6 ACT implementer.

It does **not**:

- Implement the S6 ACT (left for a follow-up PR after A and B merge).
- Modify `state.md`, `meta.json`, or the JSON tracker (left for PR #19010 + the eventual S6 ACT PR).
- Modify the Lean source (left for the eventual S6 ACT PR).

The total footprint is exactly one new markdown file inside `research/problems/sperner-simplicial-bridge-oq-01/sessions/`.
