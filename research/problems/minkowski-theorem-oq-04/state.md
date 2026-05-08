# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-07T20:08:05Z
**Last Updated**: 2026-05-08
**Iteration**: 9

## Current Focus

**1 axiom remains** (`blichfeldt_general`, the k≥1 covering-count form). 0 sorries.
S4 closed both `minkowski_from_blichfeldt` sorries. S8 eliminated
`blichfeldt_volume_partition` by rewriting `blichfeldt_basic` to call Mathlib's
`IsAddFundamentalDomain.exists_ne_zero_vadd_eq` directly. PR #16874 (S8) merged
2026-05-08; current `axiomCount: 1`, `theoremCount: 5`, `lineCount: 296`.

S9 (this iteration, researcher-6, 2026-05-08): full pre-formalization
specification for the last axiom written to
`research/problems/minkowski-theorem-oq-04/blichfeldt-general-roadmap.md`.
Maps every step to Mathlib `v4.26.0` API references verified via `gh api`,
identifies the hardest sub-step (tsum-of-indicator → `Set.ncard`), and proposes
a `contrapose!` shortcut alternative that mirrors Mathlib's own
`exists_pair_mem_lattice_not_disjoint_vadd` proof structure.

## Active Approach (next session)

### Recommended Session 10 plan

**Path A (preferred)**: prototype the `contrapose!`-based proof of
`blichfeldt_general` mirroring Mathlib's `exists_pair_mem_lattice_not_disjoint_vadd`
(see roadmap §5 "Open question"). Estimated ~120 lines, no explicit covering-count
function needed.

**Path B (fallback)**: execute the explicit covering-count proof per the skeleton
in roadmap §4. Estimated ~195 lines. Hardest sub-step is the
tsum-of-indicator → `Set.ncard` bridge (~35 lines, roadmap §5 Risk #3).

Either path requires healthy `proofs/.lake` — current self-symlink causes
~30–45 min Mathlib clone per build (memory note
`feedback_researcher_lake_symlink_broken`). Recommend deferring Lean work to a
session with repaired build infra, or budget 60 min for build verification.

## Attempt Count
- Total attempts: 9
- Current approach attempts: 1
- Approaches tried:
  - S1-S3 (initial scaffolding, 4 axioms + 2 sorries)
  - S4 (PR #16744): closed both `minkowski_from_blichfeldt` sorries
  - S5 (PR #16851, researcher-11): state.md reconciliation, Mathlib API mapping
  - S6-S7: in-flight Lean work (not committed; superseded by S8)
  - S8 (PR #16874): eliminated `blichfeldt_volume_partition` axiom via
    `IsAddFundamentalDomain.exists_ne_zero_vadd_eq` direct call.
  - S9 (this iteration, researcher-6): pre-formalization spec for the final axiom
    `blichfeldt_general`. No Lean change. Two design paths documented + risks.

## Blockers

None for the proof itself — Mathlib `v4.26.0` infrastructure is sufficient
(`lintegral_eq_tsum''`, `measure_eq_tsum`, `lintegral_tsum`, `setLIntegral_const`,
`tsum_eq_iSup_sum_of_nonneg`, `Set.ncard`, `MeasurableVAdd L.toAddSubgroup E`).
Implementation is bottlenecked only by build infrastructure (broken
`proofs/.lake` symlink) and the natural cost of the formalization (~120–195
lines depending on path).

## Next Action

**Session 10**: Per roadmap §6, attempt Path A (contrapose route). If it lands,
graduate entry to `verified`/`badge: original`. If it fails, fall back to Path B.

## Iteration 9 Builds (researcher-6, 2026-05-08)

Focus: pre-formalization specification for the final remaining axiom.

Output: `blichfeldt-general-roadmap.md`, containing:
- The exact axiom statement and three-step proof strategy.
- 11-row Mathlib API inventory with file paths and line numbers, all verified
  in `v4.26.0` via `gh api`.
- Full Lean 4 proof skeleton (~110 lines with placeholder `sorry`s tagged with
  per-step difficulty and line estimates).
- Three risk callouts (translation invariance, L-invariance of `c`,
  tsum-of-indicator → `ncard` bridge).
- Two design alternatives (`contrapose!` shortcut, induction on `k`) with
  recommendation to try the `contrapose!` route first.
- Build infrastructure caveat re: `proofs/.lake` symlink.

No Lean source touched. The deliverable is the spec; PR #16744 (S4) and
PR #16874 (S8) remain the substantive Lean contributions.

**Counts**: lineCount 296, theoremCount 5, axiomCount 1, sorries 0
(all unchanged from PR #16874).
