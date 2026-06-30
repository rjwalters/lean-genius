# Current State

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Iteration**: 1
**Status**: in-progress

## Current Focus

Empty stub (no statement). Chose the natural next result in the birthday-problem
lineage: **monotonicity of the collision probability in group size** — the formal
content of the paradox's defining intuition, which the lineage's exponential
estimates never state (researcher-9).

## Delivered (PR pending)

`proofs/Proofs/BirthdayProblemOQ02OQ01OQ03.lean` — 9 theorems, 2 defs, 0 axioms,
0 sorries (typechecked `lake env lean`, Docker down; `#print axioms` = only
propext/Classical.choice/Quot.sound):

- `collisionProb_monotone` — collision prob `1 − P(all distinct)` is
  non-decreasing in `k` for `j ≤ k ≤ d` (the monotone birthday paradox).
- `birthdayProduct_antitone` — `P(all distinct) = ∏_{i<k}(1 − i/d)` non-increasing
  in `k ≤ d`, by `Nat.le_induction` from `birthdayProduct_step_le`.
- `birthdayProduct_succ` — recurrence `P(k+1) = P(k)·(1 − k/d)`.
- `collisionProb_one` (= 0), `collisionProb_nonneg`, `collisionProb_le_one` —
  genuine probability.

## Important note

The lineage parent `BirthdayProblemOQ02OQ01.lean` (two-sided exp estimate) does
NOT compile against the current store Mathlib (v4.26.0): it uses deprecated
API (`div_le_iff`, `Finset.sum_range_id_eq_sum_range_succ_div_two`,
`Nat.eq_or_gt_of_le`). So this file is deliberately **self-contained** (imports
Mathlib only; restates the standard `birthdayProduct`), depending on no project
file. Worth flagging the parent for a separate API-refresh repair.

## Next Action

Possible follow-up: strict monotonicity (collision prob strictly increases while
`P(k) > 0`), or the half-probability threshold `k ≈ 1.177√d`.
