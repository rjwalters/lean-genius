# Current State

**Phase**: STATE-SYNC
**Since**: 2026-05-16T19:01:00Z
**Iteration**: 5

## Current Focus

S5 STATE-SYNC — bring state.md current with canonical research-JSON +
correct material axiom-count drift in `currentState.nextAction`. Slug
has been dormant since 2026-03-30 (PR #8409, unused-axiom cleanup);
state.md was still the bootstrap template (`Phase: NEW, Iteration: 1`)
even though three substantive ACT PRs (#7861, #8042, #8409) had landed.
Doc-only; no .lean / lake-manifest / leanFiles[] / gallery edits.

## Iteration History

| Session | When | Phase | PR | Net effect on `Erdos28Problem.lean` |
|---|---|---|---|---|
| S1 | 2026-03-23 | ACT | #5583 | 8 axioms → 6 (proved 2 axioms, fixed compilation) |
| S2 | 2026-03-29 | ACT | #7861 | 6 axioms → 5 (proved `basis_counting_lower`) |
| S3 | 2026-03-29 | ACT | #8042 | 5 axioms → 4 (proved `repFunction_pos_of_mem` + `total_rep_unbounded`; removed incorrect `average_rep_unbounded`) |
| S4 | 2026-03-30 | ACT | #8409 | 4 axioms → 1 (mass cleanup: removed 3 unused axioms across the file as part of repo-wide 2,256-axiom prune across 585 Erdős files) |
| S5 | 2026-05-16 | STATE-SYNC | (this PR) | doc-only — state.md catchup + JSON `nextAction` correction |

## Actual Current Lean State (as of S5, 2026-05-16)

- `proofs/Proofs/Erdos28Problem.lean` — wc -l = 214 (JSON split-length convention = 215). **1 `axiom` declaration**: `erdos_turan_conjecture` (the OPEN $500 conjecture itself — cannot be eliminated, it IS the problem). 5 theorems, 3 definitions, 0 sorries.
- `proofs/Proofs/Erdos28AdditiveBases.lean` — wc -l = 647 (JSON split-length = 648; gallery meta uses wc -l). **2 `axiom` declarations**: `grekos_lower_bound` (Grekos et al. 2003: r_A(n) ≥ 6 i.o.) and `borwein_lower_bound` (Borwein et al. 2006: r_A(n) ≥ 8 i.o.) — both deep published theorems, partial progress toward the conjecture. 15 theorems, 11 definitions, 0 sorries.

## Drift Items Corrected by S5

1. **state.md = bootstrap template** ("Phase: NEW, Iteration: 1") — replaced with reality.
2. **`currentState.nextAction` overcount** — JSON claimed "Remaining axioms: 5 in Problem file" (correct only at end-of-PR-#7861); after PR #8042 (4 axioms) and PR #8409 (1 axiom), the actual count is 1. Corrected.
3. **`currentState.focus` stale** — claimed "Session 4: Proved basis_counting_lower" but Session 4 was actually the mass-prune in PR #8409, not the basis_counting_lower work (that was Session 2 / PR #7861). Refreshed.
4. **knowledge.md Sessions log** — only the 2026-03-29 entry; missing 2026-03-29 (PR #8042) and 2026-03-30 (PR #8409). Backfilled in this S5.

## Drift Items NOT Touched by S5 (per researcher-PR-hygiene memory)

- `proofs/Proofs/Erdos28Problem.lean` content — unchanged since PR #8409.
- `proofs/Proofs/Erdos28AdditiveBases.lean` content — unchanged since PR #6840.
- `src/data/proofs/erdos-28/meta.json` — gallery metadata (`lineCount: 647`, `axiomCount: 2`) reflects `Erdos28AdditiveBases.lean` (the canonical gallery file); accurate. No edits.
- `src/data/research/problems/erdos-28.json` `leanFiles[]` — split-length convention is mechanic territory; leave to pnpm build / dedicated mechanic PR.
- `src/data/proofs/erdos-28-additive-bases/` — sibling slug already at `phase: COMPLETED / graduated`. No edits.

## Active Approach

None at present — this iteration is doc-only state synchronization.
The slug's substantive question (the $500 Erdős–Turán conjecture) is
OPEN and not attackable from current Mathlib. Future iterations could:

- Formalize the Grekos et al. (2003) lower bound `r_A(n) ≥ 6 i.o.`
  (currently axiomatized in `Erdos28AdditiveBases.lean`)
- Formalize the Borwein–Choi–Chu (2006) bound `r_A(n) ≥ 8 i.o.`
  (currently axiomatized)
- Formalize the Erdős–Fuchs (1956) fluctuation theorem
- Extend the existing `sidon_not_basis` argument toward $B_2[g]$ sets
  (already proved as `erdos_40_from_28` via the main axiom; could be
  proved unconditionally if Grekos/Borwein were formalized)

## Blockers

None — doc-only ship. Infrastructure note for future ACT iterations:

- Host disk avail at S5-time: 3.2 Gi (RED, below same-day soft floor
  ~5 Gi referenced by adjacent build-pending ACTs).
- `docker info` Server section did not respond within 5s — Docker
  daemon state ambiguous (Client responds, Server may be hung).
- Both conditions foreclose `lake build` / `docker-build.sh` at S5-time,
  reinforcing the doc-only scope choice.

## Next Action

Slug holds at 1 axiom in `Erdos28Problem.lean` (the conjecture itself)
and 2 axioms in `Erdos28AdditiveBases.lean` (Grekos/Borwein partial
results). Optional next ACT: formalize Grekos `r_A(n) ≥ 6 i.o.` —
this is the lowest-hanging axiom; the proof uses an analytic counting
argument that may be tractable. Defer pending disk/Docker recovery.

## Attempt Counts

- Total attempts: 1 (this S5 STATE-SYNC; prior S1–S4 ACTs not counted
  in the bootstrap-template counter)
- Current approach attempts: 0
- Approaches tried: 0
