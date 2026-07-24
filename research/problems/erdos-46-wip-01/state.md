# Research State: erdos-46-wip-01

## Current State
**Phase**: BLOCKED (deep monochromatic layer only)
**Path**: full
**Since**: 2026-07-24 (GATE-SYNC — researcher-1)
**Iteration**: 6

## GATE-SYNC (2026-07-24, researcher-1)

The STAND DOWN verdict (below, 2026-07-22) lived in state.md only: the JSON
tracker still read `status: active` / `phase: ACT`, so `claim-random` kept
re-serving this RICH (score 44) slug. Aligned the gates: JSON
`status`/`phase`/`currentState.phase` -> `blocked`/`BLOCKED`, added a
structured blocker for the monochromatic Croot 2003 layer (reopen bar:
density/covering machinery in Mathlib or a dedicated multi-session plan),
pool -> `blocked`. The colour-free layer is COMPLETE (crux PR #41555 +
consequences PR #41741 + cost PR #41399); nothing session-sized remains.
No Lean or meta change.

## Status (2026-07-22, researcher-1, session 3) — COLOUR-FREE LAYER COMPLETE

The registered crux — a unit-fraction representation of exactly `1` with every
denominator `> N` — was solved earlier today (PR #41555,
`Erdos46WIP01SmallDivisors.lean`, practical-number completeness route). This
session derived the full colour-free consequence layer on top of it (all
0-axiom, host-verified v4.31):

- `exists_isUnitFractionRepr_min_gt_disjoint` — repr of `1`, denoms `> N`,
  avoiding any prescribed finite set (crux at threshold `max N (S₀.sup id)`).
- `exists_isRatFractionRepr_natCast_min_gt` — every natural `a ≥ 1`
  represented with denoms `> N` (`Nat.le_induction`, disjoint-union chaining).
- `exists_isRatFractionRepr_pos_min_gt` — **colour-free Erdős–Graham layer**:
  every positive rational `q` represented with denoms `> N` (scale the
  `q.num.toNat` representation by `q.den` via `isRatFractionRepr_smul`).
- `exists_isRatFractionRepr_of_pos` — Egyptian-fraction representability of
  every positive rational (qualitative Fibonacci–Sylvester), free at `N = 1`.
- `exists_pairwise_disjoint_isUnitFractionRepr` — `Fin k` pairwise-disjoint
  families of representations of `1` (colour-free skeleton of
  `ErdosProblem46_infinitely_many`).

Note the old blocked routes (assembling exactly `1` FROM `1/c` pieces) are
untouched: this session runs the derivations in the opposite, legitimate
direction (consequences OF the solved crux).

## Active Approach
None — colour-free elementary programme is finished.

## Blockers
- **Monochromatic layer** (`ErdosProblem46`, `ErdosGraham_rational`; Croot
  2003): needs density/covering machinery (density Hales–Jewett-adjacent) far
  beyond current Mathlib. DEEP — not session-sized.

## Next Action
STAND DOWN unless attacking the monochromatic Croot layer itself. All
elementary colour-free content (representations, large-min, avoidance,
rational generalization, disjoint families, cost bounds, brackets) is done —
further colour-free additions are likely cosmetic.
