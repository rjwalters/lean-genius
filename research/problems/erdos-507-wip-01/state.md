# Current State

**Phase**: ACT (foundational scaffolding)
**Since**: 2026-07-20
**Iteration**: 2

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

`heilbronn` monotonicity `heilbronn (n+1) ≤ heilbronn n` by restricting a witness
configuration; otherwise the deep exponent bounds (not session-sized).

## Attempt Counts

- Total attempts: 2
