# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ACT (modularize-then-prove)
**Path**: full
**Since**: 2026-04-21T20:08:44+02:00
**Last Updated**: 2026-05-01
**Iteration**: 33

## Current Focus
Close the sole remaining `sorry` in `BallotProblemOQ03OQ01OQ02.lean` — the
`hook_walk_identity` dispatcher branch covering Young diagrams with **≥10 rows
AND ≥10 cols AND non-rectangular** (line 13932). All other shapes (≤9 rows,
≤9 cols via transpose duality, all rectangles, all gHookYD `[a, 1^b]`,
exactly-3 through exactly-9-row shapes) are already proved.

The file has reached **14022 lines** and exceeds the Docker 32 GB build envelope,
so the row-by-row mechanical pattern (~2200 lines per new row case, see
sessions 22–32) has hit a hard scaling wall. Further progress requires either
(a) a uniform proof that closes ≥10×≥10 in one shot, or (b) splitting the file
to restore buildability before any large additions.

## Active Approach
Three routes are characterised in
`literature/closing-the-final-sorry.md` (session 33, 2026-04-27):

- **Route A — Greene–Nijenhuis–Wilf probabilistic hook walk** (~300–400 lines).
  Recommended path. Closes all remaining shapes in one argument and replaces
  the row-by-row tower if reformulated. A deterministic recasting (counting
  weighted hook walks) avoids `ProbabilityTheory` imports.
- **Route B — Fomin growth diagrams / RSK**. Heavier infrastructure;
  contributes the SYT ↔ NI-paths bijection separately documented as the
  canonical-config LGV path in PART V comments.
- **Route C — Continue row-by-row** (PART XXVII = exactly-10-row, ~2300 more
  lines). Mechanical but rejected: each new row pushes the file further beyond
  the build envelope; reaching ≥50 rows would require ~90 K lines.

**Pre-requisite for ANY route:** modularize the file. Sessions 31–32 confirmed
that PARTS XII–XXIII (~10 000 lines of row-by-row coverage) can be split into a
dedicated module without disturbing PARTS I–XI (definitions, hook-product
infrastructure) or the corner-recursion / `hook_length_formula_general` plumbing
in PARTS XIII–XIV.

## Attempt Count
- Total attempts: 33 (sessions 1–33; sessions 1–4 archived to
  `sessions/`; sessions 5–33 in `knowledge.md`)
- Current approach attempts: 0 (GNW route not yet attempted)
- Approaches tried:
  1. LGV-determinant via `lgv_lemma_rxr` + Jacobi–Trudi (sessions 1–10) —
     blocked on `ni_count_eq_syt_count` and `lgv_det_factors_as_hook_quotient`;
     deleted as dead scaffolding in session 32.
  2. Corner recursion via `card_SYT_corner_step` + `hook_walk_identity`
     (sessions 11–14) — successful: gave `hook_length_formula_general`
     modulo a single `hook_walk_identity` sorry.
  3. Row-by-row dispatch on `hook_walk_identity` (sessions 15–30) —
     successful for ≤9 rows / ≤9 cols (transpose duality) / all rectangles;
     hit file-size wall at session 30.
  4. Housekeeping: dead-code removal and LGV restatement as comments
     (sessions 31–33).

## Blockers
- **File size beyond Docker envelope.** At 14022 lines
  `BallotProblemOQ03OQ01OQ02.lean` cannot be type-checked under the standard
  `./proofs/scripts/docker-build.sh` invocation (32 GB memory limit). All
  edits since session 27 are *unverified by the build*. Modularization is
  required before any further large additions.
- **No probabilistic toolkit imported.** Route A in its classical form leans
  on uniform sampling and conditional probability machinery from
  `Mathlib.MeasureTheory` / `Mathlib.ProbabilityTheory`. Transitive import
  weight may further worsen the build envelope problem; a deterministic
  weighted-walk recasting is preferred.

## Next Action
**OBSERVE → PLAN — file modularization, then GNW.**

1. Map the dependency graph between PARTS in `BallotProblemOQ03OQ01OQ02.lean`
   to identify a clean cut-line. Candidate split:
   - `BallotProblemOQ03OQ01OQ02Core.lean` ← PARTS I–XI + XIII–XIV
     (definitions, `hookProd`, `hookProd_ratio_formula`, corner recursion,
     `hook_length_formula_general` modulo `hook_walk_identity`).
   - `BallotProblemOQ03OQ01OQ02RowCases.lean` ← PARTS XII + XV–XXIII
     (per-row dispatchers and `hook_walk_identity_*Row` lemmas).
   - `BallotProblemOQ03OQ01OQ02.lean` (top-level): imports the two above,
     re-exports `hook_length_formula` and `hook_length_formula_general`.
2. Verify each part compiles independently (or at least the Core file does)
   under Docker.
3. Once the Core file builds, attempt Route A (deterministic GNW recasting)
   in a fresh `BallotProblemOQ03OQ01OQ02HookWalk.lean` companion.

If modularization itself proves to be larger than a single session, scope down
to extracting only the `hook_walk_identity_*Row` lemmas (PARTS XV–XXIII) into
the row-cases module; the dispatcher itself stays in the main file as a thin
case split.

## References

- `literature/closing-the-final-sorry.md` — three-route comparison (session 33)
- `knowledge.md` §Session 32 — dead-code removal and LGV restatement
- `knowledge.md` §Session 31 — file-size wall first hit
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02.lean:13932` — the sole remaining sorry
