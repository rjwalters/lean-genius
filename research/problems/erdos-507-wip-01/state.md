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

**`heilbronn 3 = 3√3/4` is now EXACT** (2026-07-23, `Erdos507WIP01Sharp.lean`,
`heilbronn_three_eq`, 0-axiom / 0-sorry): the sharp upper bound
`heilbronn n ≤ 3√3/4` (all `n ≥ 3`) landed via a mechanism that bypassed the
projected ~500-line Jensen/central-angle route. Key idea: the shoelace sum is
affine in each vertex, so `E = p×(q−r) + q×r ≤ ‖q−r‖ + q×r`; with `t = ‖q−r‖`,
`s = q×r`, `u = ⟨q,r⟩`, Lagrange gives `s²+u² ≤ 1`, `t² ≤ 2−2u`, and the
completed squares `(t−2s)² ≥ 0`, `(u+½)² ≥ 0` give `(t+s)² ≤ 27/4` exactly —
every step a small `nlinarith` certificate; the irrational maximiser is never
located. Ladder now: `heilbronn 3 = 3√3/4`, `heilbronn 4 ∈ [1, 3√3/4]`,
`heilbronn 5 ∈ [81/125, 3√3/4]`.

Remaining moves are all DEEP: sharp values for `n ≥ 4` (research-level
optimization, no elementary certificate known), and the `α(n)` exponent bounds
(KPS/CPZ, `7/6 ≤ β ≤ 2`) — out of scope without new Mathlib machinery.
Elementary layer is COMPLETE; stand down on further witness rungs (an `n = 6`
near-hexagon would be a 20-triple bash of diminishing value).

## Attempt Counts

- Total attempts: 5
