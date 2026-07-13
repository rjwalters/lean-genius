# Current State

**Phase**: COMPLETED
**Since**: 2026-05-16 (researcher-11, S2 STATE-SYNC — close drift from gallery+JSON-inner+Lean)
**Iteration**: 2

## Current Focus

State-sync: gallery `meta.json` (status `verified`, 0 sorries, 0 axioms,
169 LOC, 12 theorems) and research JSON `currentState.phase = DONE`
already reflect completion, but this `state.md` was stuck at the
2026-04-03 bootstrap (phase NEW, iteration 1, "Begin problem
exploration") and JSON top-level `phase: ACT` / `status: active` were
not flipped. This sync closes that drift and unblocks claim-random from
re-serving the slug.

## Active Approach

Closed. The proof in `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01.lean`
(169 LOC, 12 theorems, 0 sorries, 0 axioms) directly establishes the
descending-factorial analogue of the arithmetic series identity:

- `choose_descFactorial`: `C(n,k) · k! = n.descFactorial k`
- `choose_product`: `C(n,k) · k! = ∏ i ∈ range k, (n − i)`
- `choose_full_factorial`: `C(n,k) · k! · (n−k)! = n!`
- `factorial_dvd_descFactorial`: `k! | n.descFactorial k`
- `ascending_descending_duality`: bridges to OQ-02-OQ-04 ascending form
- Plus specialisations at `k = 1, 2, 3` and concrete numeric checks

Key Mathlib bearer: `Nat.descFactorial_eq_factorial_mul_choose`.

## Blockers

None.

## Iteration History

| Iter | Date | Researcher | Type | Outcome |
|---|---|---|---|---|
| 0 | 2026-04-03 | seeker/aristotle | SCAFFOLD | bootstrapped problem.md + state.md (NEW) |
| 1 | (pre-2026-04-27) | researcher | ACT | proved 12 theorems in `ArithmeticSeriesOQ02OQ04OQ01.lean` (0 sorries, 0 axioms); gallery `meta.json` updated to `verified` |
| 2 | 2026-05-16 | researcher-11 | STATE-SYNC | THIS — close drift between state.md / JSON top-level (`phase: ACT`, `status: active`) and gallery (`status: verified`) / JSON inner (`currentState.phase: DONE`) |

## Next Action

None — work complete; gallery `meta.json` and Lean file in sync. After
this PR merges, the slug should drop off `claim-random`'s candidate pool
(JSON top-level `phase` → `DONE`, `status` → `completed`).

## Attempt Counts

- Total attempts: 2 (1 ACT — Lean proof, 1 STATE-SYNC — this PR)
- Current approach attempts: 0 (no active research)
- Approaches tried: 1
