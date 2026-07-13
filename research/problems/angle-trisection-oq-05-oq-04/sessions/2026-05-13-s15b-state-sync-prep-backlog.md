# S15b STATE-SYNC — PREP backlog catch-up (S9–S15) + S16 ACT target set (doc-only)

**Researcher**: researcher-4
**Date**: 2026-05-13 (~21:00 UTC; ~12h after S15 PREP #18704 merged 09:22 UTC)
**Phase**: STATE-SYNC (doc-only)
**Iteration**: 15b (post-S15 PREP merged; 0 ACT iterations since S8)
**Predecessors**: all merged S1–S15 (see `state.md` session log table)

**Build status**: not applicable — doc-only state-sync, no Lean changes.

## Why this STATE-SYNC

`state.md` head was frozen at S8 (ACT, Iteration 8, 2026-05-12) since
PR #18195 merged 2026-05-12 23:20 UTC. Between S8 and now, **8 PREP-only
PRs (S9-OBSERVE, S9-PREP, S10, S11, S12, S13, S14, S15)** merged to main
without any `state.md` refresh. Anyone reading `state.md` would see:

- "Phase: ACT — close the parallel case of HH-3"
- "Iteration: 8"

…while in reality the parallel case has been merged for ~18 hours and
the file has accumulated:

- S9-O + S9-P: HH-3 intersecting Real.sqrt-bisector blueprint
- S10: HH-5 parent statement refuted with explicit counterexample
- S11: HH-6 cubic-real-root extraction blueprint
- S12: `HHAxioms` instantiability audit
- S13: HH-7 parallel-`P ∉ ℓ₁` sub-case re-audit identifying `l = ℓ₂` branch
- S14: refutation of S11 §4 D3 with concrete `(p₁=(0,1), p₂=(0,2), ℓ=y=0)` witness
- S15: HH-6 same-directrix slope-quadratic in normal form
  `(y₁−y₂)m² + 2(x₁−x₂)m − (y₁−y₂) = 0` with `Disc = 4·‖p₁−p₂‖²`,
  plus a one-page Lean S16 ACT blueprint

The PREP backlog matters: it is the active research output for the slug.
But it is **blueprint, not implementation**. The Lean file is still at
the S8 surface area (1144 lines, 26 theorems, 10 definitions, 3 sorries),
and the next move is S16 ACT — picking ONE of the three open HH-axiom
gaps (HH-3 intersecting, HH-5 conditional, HH-6 same-directrix) and
converting its blueprint to proved Lean.

## What this PREP ships

A `state.md` rewrite (~190 lines, replacing the 333-line S8-era file)
plus this session-notes file. Zero edits to:

- `proofs/Proofs/AngleTrisectionOQ05.lean` or
  `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` (no Lean changes).
- `knowledge.md`, `problem.md` (citations and OQ statement unchanged).
- `src/data/proofs/angle-trisection-oq-05-oq-04/*` (meta.json,
  annotations.json, index.ts — meta drift is auditor/mechanic territory
  per the linecount/title sweep memory; canonical writer
  `enrich-research.ts` may refresh title/description anyway).
- Any merged session note (S1–S15; retroactive correction is auditor/
  mechanic territory).
- The open PR #18192 file path (obsolete S8 SCAFFOLD).
- Any other slug's files.

## What `state.md` now contains (post-S15b)

1. **Header** — Phase: PREP, Since: 2026-05-13 (S15 merge), Iteration: 15.
2. **Current Focus** — one paragraph naming the eight merged PREP
   iterations and the recommended S16-α target (HH-6 same-directrix).
3. **HH-axiom Programme Status** — 12-row spectrum table covering each
   axiom (split where sub-cases differ) with "Lean status" (ACT merged
   vs PREP only) + "Coverage" + reference PR list.
4. **Sorries & Axiom Inventory** — exact unchanged counts (0 `axiom`
   declarations, 1 structure-encoded `ftCompatible` assumption, 3
   intentional sorries on the S3/S4/S5 OQ targets, 26 theorems, 10
   definitions, 1 structure).
5. **Next Action (S16+)** — three labelled candidates with concrete
   sub-deliverables and Real.sqrt API list:
   - S16-α (recommended): HH-6 same-directrix `belochFold_sameDirectrix`
     ~150-200 lines, four supporting lemmas, assembly into
     `hh6_existence_sameDirectrix`.
   - S16-β: HH-3 intersecting Real.sqrt unit-normal bisector ~200 lines.
   - S16-γ: HH-5 conditional parent-file edit (larger blast radius;
     defer until S16-α or S16-β lands).
   - Anti-target: HH-6 *distinct-directrix* (cubic root, ~300 lines,
     missing Mathlib parabola-tangent API).
6. **Open PR awareness** — flags orphaned PR #18192 (S8 SCAFFOLD).
7. **Session Log** — 17-row table covering S1 → S15 + S15b.
8. **Honest Calibration** — explicit 0/0/0/0/0 (Lean LOC / sorries /
   conjectures / theorems / HH ingredients) plus what the STATE-SYNC
   does change (Phase line, session log entries, spectrum table refresh,
   S16 target).
9. **References Captured** — S1-S8 set plus S10-PREP-added Justin 1991,
   Hull 2003, Lang 2010 (HH-5 conditional literature).

## Why not also refresh `meta.json` title / description

`meta.json` is governed by canonical writer
`scripts/research/enrich-research.ts` (per the `linecount_drift_class`
memory). Title and description ARE manually maintained and currently
stale ("S8 — constructive HH-3 parallel case"), but:

- The description field is ~3500 characters; refreshing it for S9-S15
  would be ~30 lines of meta.json diff that may be overwritten the next
  time `enrich-research.ts` runs.
- The sibling-PR-out-of-scope-don't-ship pattern applies: if the next
  Builder/Mechanic/Auditor sweep wants to refresh title/description, it
  will do so atomically.
- This PR is intentionally **narrow** — state.md is the canonical "what
  happened recently" doc for `research/problems/<slug>/`, and that is
  the only file that has gone stale. (`knowledge.md` and `problem.md`
  remain correct; the math hasn't changed.)

A follow-up "meta.json title/description refresh for S9-S15" can ride
on the next S16 ACT PR (which will already touch meta.json for line
count + theorem count) — appending it now would be churn.

## Pre-claim race-check (2026-05-13 ~21:00 UTC)

- `gh pr list -R rjwalters/lean-genius --search "angle-trisection-oq-05-oq-04 in:title" --state open` →
  PR #18192 (S8 SCAFFOLD, build pending, obsoleted by merged #18195).
  Does **not** touch `state.md` (only `proofs/Proofs/...` and
  `src/data/proofs/...`).
- `git worktree list | grep angle-trisection-oq-05-oq-04` → no in-flight
  worktrees other than my own (researcher-4 working copy).
- `gh pr list -R rjwalters/lean-genius --search "angle-trisection-oq-05-oq-04 STATE-SYNC in:title" --state all` →
  no prior STATE-SYNC PR on this slug (this is the first).

No race.

## Anti-targets (this S15b explicitly does NOT do)

- Do not add Lean (this is a STATE-SYNC, not S16 ACT).
- Do not touch `meta.json` (drift class deferred to enrich sweep).
- Do not touch `knowledge.md` or `problem.md` (unchanged).
- Do not retroactively edit S9-S15 session notes (S14 PREP itself
  documents that retroactive correction is auditor/mechanic territory).
- Do not close PR #18192 (author's call; only flag it).
- Do not start S16 ACT in the same PR (would mix scopes).
- Do not refresh other-slug state.md or any audit-tracker JSON.

## Honesty / what could be wrong

1. **HH-3 intersecting blueprint maturity.** S9 PREP is a survey of the
   Mathlib `Real.sqrt` API surface plus a translation of the standard
   angle-bisector formula. It does not exhibit closed-form fold-line
   coefficients the way S15 PREP does for HH-6 same-directrix. The
   S16-α recommendation (HH-6 same-directrix) is partly motivated by
   blueprint readiness, not just mathematical priority.

2. **HH-7 sliver characterisation.** S13 PREP identified that the S6/S7
   spec missed the `l = ℓ₂` branch — i.e. the "unsatisfiable sliver" is
   actually a 2-conjunct condition `crossDet = 0 ∧ P ∉ ℓ₁ ∧ l ≠ ℓ₂`,
   not just `crossDet = 0 ∧ P ∉ ℓ₁`. The merged S7 Lean ACT does NOT
   reflect this refinement; the file's `hh7_existence_p_on_ℓ₁` is still
   correct, but the prose comment about the "genuinely unsolvable
   corner" is technically narrower than the file claims. Cleaning this
   up is a 5-LOC docstring-only edit and could ride on the S16 ACT PR.

3. **PR #18192 status.** I cannot verify whether the author intends to
   close it or rebase it. The merged S8 PR #18195 chose the
   "translate-bisector" (`parallelBisector`) construction over the
   "midparallel fold" of #18192, so #18192 cannot be merged without
   conflict resolution. Flagged in state.md; not closed.

4. **State.md size reduction.** The new state.md is ~190 lines, down
   from 333. The S8-era body was a single-iteration deep-dive (PART 10
   spec in prose). The S15b version summarises *eight* iterations at
   the table level; per-iteration detail lives in `sessions/` files.
   This trade-off matches the
   `feedback_researcher_state_sync_active_thread_prep_backlog` pattern.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | `gh pr list ... --state open --search "angle-trisection-oq-05-oq-04 in:title"` returned only obsolete PR #18192; no fresh STATE-SYNC PR | clean to proceed |
| 2 | `git switch -c research/angle-trisection-oq-05-oq-04-s15b-state-sync-... origin/main` | fresh branch off post-S15 main |
| 3 | Read 8 merged session-log TL;DRs (S9-O, S9-P, S10, S11, S12, S13, S14, S15) to extract per-iteration deliverables for the spectrum table | source-of-truth aligned |
| 4 | Rewrote `state.md` (333 → ~190 lines): Phase ACT/Iter 8 → PREP/Iter 15; added "HH-axiom Programme Status" 12-row table with Lean status; concrete S16-α target with sub-deliverables; 17-row session log table; flagged orphan PR #18192; honest calibration block | state.md now reflects post-S15 reality |
| 5 | Wrote this session log (`2026-05-13-s15b-state-sync-prep-backlog.md`) with anti-targets, race-check, and honesty caveats | session log appended |
| 6 | Did NOT touch meta.json title/description (drift class deferred per memory) | clean scope |
| 7 | (pending) Commit + push + PR via `gh api -X POST repos/.../pulls` (fallback) with title `STATE-SYNC — 8 merged PREPs (S9-S15) catch-up; S16 ACT target set (doc-only)` | next |

## File summary

- Modified: `research/problems/angle-trisection-oq-05-oq-04/state.md` (333 → ~190 lines)
- Added: `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-13-s15b-state-sync-prep-backlog.md` (this file)
- Untouched: everything else (Lean files, knowledge.md, problem.md, meta.json, annotations.json, index.ts, prior session logs, other slugs)
