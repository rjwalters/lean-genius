# Current State

**Phase**: COMPLETED (gallery-verified, tracker-synced)
**Since**: 2026-06-02 (tracker promotion — Lean originally landed 2026-05-03 via PR #15268)
**Iteration**: 2

## S2 STATE-SYNC — 2026-06-02 (researcher-1, this PR, doc-only)

Promotes the slug's `currentState.phase` from stale "NEW" to "COMPLETED"
to match the actual on-main state. The Lean deliverable
`proofs/Proofs/DesarguesTheoremOQ01OQ01.lean` (297 LOC, 0 axioms, 0 sorries)
was merged 2026-05-03 via PR #15268 and the gallery entry
`src/data/proofs/desargues-theorem-oq-01-oq-01/` was created in PR #15421
(2026-05-04T01:20Z). The gallery has since been enriched four times
(#15358, #15497, #15858, #15886, #17429, #20282, #20856, #20922, #20932,
#20952). Only the slug's `state.md` head and JSON tracker remained at
their stub form from initial seeker creation (2026-05-03T11:41Z).

## What is COMPLETED

`proofs/Proofs/DesarguesTheoremOQ01OQ01.lean` (`namespace MoultonPlane`,
297 LOC, verified on main):

- **Definitions** (12):
  - `onMoultonLine (m b : ℝ) (P : ℝ × ℝ) : Prop` — piecewise Moulton line:
    `m ≤ 0` ordinary affine; `m > 0` bent at `x = 0` (slope `m/2` on right
    half-plane). Captures Moulton 1902 construction.
  - `MoultonCollinear (P Q R : ℝ × ℝ) : Prop` — three-point collinearity
    in the Moulton plane.
  - 10 private definitions: the 10-point counterexample data
    (`O_pt`, `A_pt`, `B_pt`, `C_pt`, `A'_pt`, `B'_pt`, `C'_pt`,
    `P_pt = (-17, 9)`, `Q_pt = (27, 17)`, `R_pt = (-6, 11)`).

- **Theorems** (30):
  - 6 unfolding helpers (`onML_neg_slope`, `onML_pos_left`, `onML_pos_right`,
    `onML_eq_neg`, `onML_eq_pos_left`, `onML_eq_pos_right`).
  - 3 perspectivity collinearities (`collinear_OAA'`, `collinear_OBB'`,
    `collinear_OCC'`) — `O`-perspective of triangles `ABC` and `A'B'C'`
    verified by `norm_num` on the linear-relation form of `onMoultonLine`.
  - 18 side-incidence checks (`P_on_AB`, `A_on_AB`, …, `R_on_C'A'`,
    `A'_on_C'A'`) — every counterexample point lies on its declared side.
  - `desargues_fails : ¬ MoultonCollinear P_pt Q_pt R_pt` — the heart of
    the argument. Two-case split on `m ≤ 0` (ordinary side closes via
    `linarith`: `44m = 8` impossible for `m ≤ 0`) vs `m > 0`
    (right-half-plane bent side closes via `linear_combination` to extract
    `11m = 2` and `61m = 16` then `linarith` derives the contradiction
    `122 = 176`).
  - `moulton_counterexample : ∧[19 conjuncts]` — the packaged certificate
    bundling all incidence checks and the non-collinearity conclusion.

- **Counts**: 0 axioms, 0 sorries, 30 theorems, 12 definitions, 297 LOC.

## Why this answers the slug's question

The slug asks "Can we formalize non-Desarguesian projective planes in Lean
to demonstrate when the theorem fails?". The on-main deliverable answers
in the **affine** form: the Moulton plane is a non-Desarguesian affine
plane over ℝ and the formalized counterexample `moulton_counterexample`
exhibits a triangle pair in perspective from `O = (0, 0)` whose
corresponding sides intersect at `P, Q, R` that are *not* Moulton-collinear,
even though they ARE Euclidean-collinear (so Desargues holds in ordinary
ℝ²). This proves Desargues's theorem is independent of the affine plane
axioms — it requires additional algebraic structure (commutativity of the
ternary ring / coordinatization by a field or division ring).

The *projective* form (extending the Moulton plane by a line at infinity
and reformulating the counterexample projectively) is a natural follow-up
captured in `knowledge.nextSteps` as oq-01. The *finite* form (Hall plane
of order 9, smallest finite non-Desarguesian plane) is captured as oq-02.

## Open follow-ups (NOT in this PR)

These are listed in `knowledge.nextSteps` and remain available for future
ACT iterations:

- **oq-01**: Extend to projective completion (add line at infinity) and
  prove Desargues fails in projective Moulton plane.
- **oq-02**: Formalize smallest finite non-Desarguesian plane (Hall plane,
  order 9).

Neither is in scope for this STATE-SYNC.

## S2 STATE-SYNC deliverable

3 files:

1. `research/problems/desargues-theorem-oq-01-oq-01/state.md` (this file)
   — head replaced with COMPLETED narrative.
2. `src/data/research/problems/desargues-theorem-oq-01-oq-01.json` —
   `currentState.phase` `NEW` → `COMPLETED`; `iteration` 1 → 2;
   `since` / `focus` / `nextAction` / `lastUpdate` refreshed.
3. NEW `sessions/2026-06-02-s2-statesync-completed.md` — session memo.

No Lean / gallery / sibling / problem.md / knowledge.md edits. The
on-main Lean deliverable is unchanged.

## Race-safety

`gh pr list --search "desargues-theorem-oq-01-oq-01" --state open` returned
`[]` at claim time. Most recent activity is enrichment PR #20952
(2026-05-29T14:04Z, four days prior). Quiet slug, no race risk.

## After this STATE-SYNC

The claim should be released with `claim-problem.sh update <slug> completed`
to migrate the slug from `in-progress` (transient) into the `completed`
pool, matching the actual verification status. Future researcher
claim-random calls will not re-claim this slug from the `completed`
bucket (per the script's standard behavior).

If a future researcher wants to pursue oq-01 (projective completion) or
oq-02 (Hall plane), they should open a new follow-up slug rather than
re-opening this one.
