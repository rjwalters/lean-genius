# Research State: erdos-46-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T17:33:18-07:00
**Iteration**: 3

## Status (2026-07-22, researcher-1) — two-sided bracket of 1 (denoms > N, vanishing width)

The `Erdos46Problem.lean` parent already carries a rich 0-axiom elementary toolkit for
unit-fraction representations (telescoping `sum_Ico_inv_mul_succ` / `isRatFractionRepr_telescope`,
divisor-sum route `isUnitFractionRepr_of_divisorSum` + `divisorSum_min_gt`, the harmonic-tail
bounds `sum_Ico_inv_ge_half/ge_one`, and the two controlled approximations
`exists_isRatFractionRepr_controlled_overshoot` (`1 ≤ q < 1+1/(N+1)`, denoms > N) and
`exists_isRatFractionRepr_controlled_undershoot` (`1-1/(N+1) ≤ q < 1`, denoms > N)).

This session added `exists_isRatFractionRepr_bracket_one (N) (hN : 1 ≤ N)` (0-axiom,
docker-verified `[propext, Classical.choice, Quot.sound]`): a single packaged witness
sandwiching `1` — `∃ Slo Shi qlo qhi`, both reprs with denoms > N, `qlo < 1 ≤ qhi`, and the
**explicit vanishing width** `qhi - qlo < 2/(N+1)`. As `N → ∞` the bracket collapses onto `1`.
This is the exact launching point an *exact* landing on `1` would refine.

## Active Approach
Elementary unit-fraction toolkit + controlled overshoot/undershoot bracketing `1` with
denominators > N. The exact-landing step is the genuine open crux (below).

## Blockers
- **Exact landing on `1` with denominators > N** (close the residual `[qlo, qhi]` gap
  collision-free) = a bounded-rational Diophantine subset-sum. This is the hard nugget; the
  two-sided bracket now pins it to a `< 2/(N+1)`-wide window but does not close it elementarily.

## Next Action
Attempt the exact-landing subset-sum inside the bracketed window (or the denominator-inflation
route: repeatedly split the smallest term `1/m = 1/(m+1) + 1/(m(m+1))` to push all denoms > N,
handling collisions). If neither is session-sized, STAND DOWN — the near-1 bracket layer is
complete.
