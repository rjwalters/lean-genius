# Knowledge: birthday-problem-oq-02-oq-01-oq-03

## Summary

The birthday-problem collision probability is **monotone non-decreasing** in the
number of people: with `d` equally likely birthdays, adding people can only raise
the chance that two share a birthday.

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/BirthdayProblemOQ02OQ01OQ03.lean`, namespace
`BirthdayProblemOQ02OQ01OQ03`, 0 axioms / 0 sorries:

- `birthdayProduct k d := ∏_{i<k}(1 − i/d)` — P(all distinct)
- `collisionProb k d := 1 − birthdayProduct k d`
- `birthdayProduct_succ : P(k+1) = P(k)·(1 − k/d)`
- `birthdayProduct_step_le : k ≤ d → P(k+1) ≤ P(k)`
- `birthdayProduct_antitone : j ≤ k → k ≤ d → P(k) ≤ P(j)`
- `collisionProb_monotone : j ≤ k → k ≤ d → collisionProb j d ≤ collisionProb k d`
- `collisionProb_one : collisionProb 1 d = 0`
- `collisionProb_nonneg`, `collisionProb_le_one` (genuine probability)

## Proof idea

The recurrence `P(k+1) = P(k)·(1 − k/d)` (Finset.prod_range_succ) multiplies a
nonnegative quantity by a factor in `[0,1]`, so it cannot increase — one-step
antitone. Globalize by `Nat.le_induction`. Complement gives collision monotone.

## Gotchas

- The induction `induction k, hjk using Nat.le_induction` keeps the side
  hypothesis `hk : k ≤ d` in context referencing the current `k` (it is NOT
  reverted into the goal), while the IH *does* carry the `k ≤ d →` arrow. So the
  cases need NO `intro`; in `succ` use `(step_le hd (by omega)).trans (ih (by omega))`.
- Parent `BirthdayProblemOQ02OQ01.lean` is BROKEN against current Mathlib
  (deprecated `div_le_iff`, `Finset.sum_range_id_eq_sum_range_succ_div_two`,
  `Nat.eq_or_gt_of_le`) — could not build its olean. Kept this file self-contained.

## Approaches Tried

- Attempted to import the parent for the exponential bound: blocked (parent does
  not compile). Self-contained monotonicity needs only the product recurrence, so
  the dependency was unnecessary.
