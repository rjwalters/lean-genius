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

## Session 2026-06-28 (researcher-3) — strict monotonicity + pigeonhole certainty

**Mode**: ACT. The headline (non-strict monotonicity, boundary, well-formedness) was already
complete & 0-axiom, so this session added the two classic facts the file lacked. **Outcome**:
verified increment. `BirthdayProblemOQ02OQ01OQ03.lean` 136→212 L, +7 theorems, 0-axiom
(`#print axioms` = propext/Classical.choice/Quot.sound). Single-file `lake env lean` exit 0.
File imports only Mathlib (no project dep oleans needed).

### Delivered
- `factor_pos` (i < d → 0 < 1 − i/d) and `birthdayProduct_pos` (k ≤ d → 0 < P): P(all
  distinct) is strictly positive in the meaningful range.
- `birthdayProduct_step_lt` (0 < k ≤ d → P(k+1) < P(k)) — strict one-step via
  `mul_lt_mul_of_pos_left` (factor < 1 on a strictly positive product).
- `birthdayProduct_strict_lt` (0 < j < k ≤ d → P(k) < P(j)) — glued from the non-strict
  `birthdayProduct_antitone` (j+1 ≤ k) and the strict step at j: `lt_of_le_of_lt`.
- `collisionProb_strict_lt` — **strict** monotone birthday paradox (strengthens the existing
  non-strict `collisionProb_monotone`).
- `birthdayProduct_eq_zero_of_gt` (d < k → P = 0) via `Finset.prod_eq_zero` at i = d
  (`1 − d/d = 0`, `div_self`); `collisionProb_eq_one_of_gt` (d < k → collision = 1) —
  **pigeonhole certainty**.

### Gotchas
- `birthdayProduct_antitone` expects `j + 1 ≤ k`; pass `(by omega)` from `j < k` rather than
  relying on Nat.lt defeq.
- `positivity` will NOT prove `0 < (k:ℝ)/d` from `0 < k` (ℕ) — cast first
  (`exact_mod_cast`) then `div_pos`.

### Status
Formal target (monotonicity + boundary + well-formedness) was already fully proved; this
strengthens it to strict and adds the pigeonhole-certain regime. Problem is essentially
complete; remaining directions would be the exponential two-sided estimates (parent
OQ-02-OQ-01 file, which is BROKEN vs current Mathlib — deprecated `div_le_iff` etc.).
