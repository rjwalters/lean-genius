# Current State

**Phase**: ACT (foundational scaffolding)
**Since**: 2026-07-20
**Iteration**: 3

## Current Focus

Elementary, axiom-free structural facts about `minTriangleArea` and `heilbronn`
built on the already-verified `triangleArea` geometry. The deep `α(n)` growth
exponent (`7/6 ≤ β ≤ 2`, KPS lower / CPZ upper bounds) is out of scope — no
Heilbronn-specific machinery exists in Mathlib and the gap is a genuine open
research problem.

## Active Approach

Descend the nine-fold nested `⨅` of `minTriangleArea` with `ciInf_le_of_le`,
discharging every `BddBelow` side condition from nonnegativity of `triangleArea`
(the empty-index junk value over `ℝ` is `0`, so no nonemptiness hypotheses are
needed). Bound `heilbronn n` (`n ≥ 3`) via `Real.sSup_le` + `triangleArea_le_three`
+ `Finset.two_lt_card_iff`.

## Blockers

- The `α(n)` growth exponent via elementary planar geometry is deep-blocked
  (route: elementary planar geometry; reopen: materially new mechanism required).
  Only the elementary well-definedness/finiteness scaffolding is session-sized.

## Next Action

Elementary layer is now essentially complete: well-definedness, monotonicity,
the `n=3` sandwich `[3√3/4, 3/2]`, and **quantitative decay** `heilbronn n ≤ 4/m`
(`heilbronn_le_four_div`) hence `heilbronn n → 0` (`heilbronn_tendsto_zero`, added
2026-07-21). Remaining plausible elementary target: the sharp
`heilbronn 3 ≤ 3√3/4` (largest inscribed triangle, ~500-line optimization). The
deep `α(n)` exponent bounds (KPS/CPZ, `7/6 ≤ β ≤ 2`) remain out of scope.

## Attempt Counts

- Total attempts: 4
