# Research State: erdos-268

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-04-21
**Iteration**: 3
**Completed**: 2026-04-25T12:53:24.156Z (registry); STATE-SYNC 2026-05-17
**Selected by Seeker**: 2026-04-21

## Current Focus
S3 STATE-SYNC — long-completed slug with research-wave-bypass + state.md
mass-imported via unrelated sweep PR + research JSON / pool drift catchup
(doc-only).

The active research arc (S3–S7, 2026-04-21 → 2026-04-23, PRs #10920, #11210,
#11277, #11304, #11460, #11504, #11983) eliminated all open sorries of
`Erdos268Problem.lean` by completing d=0 / d=1 path-connectedness and
axiomatizing the d≥2 general case (Kovač-Tao 2024). The registry was flipped
to `phase=COMPLETED, status=graduated` on 2026-04-25 but this slug's
`state.md` was never re-written off the iter-2 OBSERVE template, and the
research JSON's `currentState.phase` likewise stayed `OBSERVE` while
`top-level phase / status` were updated.

On 2026-05-16 sperner PR #19454 (a Lean ACT for a different slug) directory-
swept this template back into `research/problems/erdos-268/state.md` via
`git mv`-style re-import — git log of state.md shows that PR as its creator
even though zero content changes were made.

This STATE-SYNC catches up four surfaces on top of `main`:
1. `state.md` head: OBSERVE/iter-2 → COMPLETED/iter-3 + iteration history.
2. `research JSON.currentState.phase`: OBSERVE → COMPLETED + iter 2 → 3
   + since 2026-04-21 → 2026-05-17 + focus/nextAction rewrites + top-level
   `lastUpdate` added.
3. `research JSON.leanFiles[]` numeric drift (3 files, 4 fields):
   - `Erdos268Aristotle.lean`: `lineCount 143 → 142`
   - `Erdos268Problem.lean`: `lineCount 952 → 979`, `theoremCount 19 → 34`,
     `defCount 15 → 17`
   - `Erdos268ProblemAristotle.lean`: `lineCount 213 → 212`
4. NEW `research/problems/erdos-268/sessions/2026-05-17-S3-STATE-SYNC.md`
   memo with full audit trail (10 sections, ~280 LOC).

## Active Approach
None — slug is COMPLETED. Two axioms remain by design (deferred to upstream
Kovač-Tao 2024 mathematics):
- `erdos_268_solved`: encodes interior nonemptiness for all d (Kovač 2024)
- `harmonicPointSet_path_connected_large`: encodes d≥1 path-connectedness
  (Kovač-Tao 2024)

Gallery `src/data/proofs/erdos-268/meta.json` correctly reflects
`status: axiomatized, badge: axiom, axiomCount: 2, sorries: 0` and all
structured numeric fields (`lineCount: 979`, `theoremCount: 34`,
`definitionCount: 17`) ALREADY match the actual Lean source — only the
research-local JSON `leanFiles[]` was stale. No meta.json edits in this PR.

## Iteration History
| # | Date | Phase | Slug | Result |
|---|------|-------|------|--------|
| 1 | 2026-04-21 | OBSERVE | seeker-select | Initial Seeker selection (PR #11071) |
| 2 | 2026-04-21 → 2026-04-23 | ACT (research wave) | 7 substantive PRs | d=0/d=1 path-connected proved; d≥2 axiomatized; final `aaafddfae68` 2026-04-23 axiomatizes the path-connectedness sorry. Registry graduated 2026-04-25T12:53:24Z. PRs: #10920, #11210, #11277, #11304, #11460, #11504, #11983 |
| 3 | 2026-05-17 | COMPLETED | S3 STATE-SYNC (this PR) | Doc-only drift catchup: `state.md` head, research JSON `currentState`, `leanFiles[]` 4-field, sessions memo. Post-merge pool flip `in-progress → completed` |

## Attempt Count
- Total attempts: 7 substantive (S2 research wave) + 1 STATE-SYNC (S3, this PR)
- Current approach attempts: N/A (COMPLETED)

## Blockers
None. Upstream Kovač-Tao 2024 formalization in Mathlib remains the path to
discharge the two remaining axioms (`erdos_268_solved`,
`harmonicPointSet_path_connected_large`).

## Next Action
Post-merge:
1. Pool flip via `scripts/research/claim-problem.sh update erdos-268 completed`
   (currently `status: in-progress` in `.lean/state/candidate-pool.json`,
   exhibiting the documented 728-slug systemic registry-vs-pool drift).
2. None pending in research arc — slug COMPLETED.

If/when Kovač-Tao 2024 path-connectedness lands in Mathlib, replace the
`harmonicPointSet_path_connected_large` axiom in `Erdos268Problem.lean` with
a proof and revisit `Erdos268ProblemAristotle.lean` (1 sorry remains there).
