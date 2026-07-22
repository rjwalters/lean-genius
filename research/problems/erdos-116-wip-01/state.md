# Research State: erdos-116-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-20
**Iteration**: 2

## Current Focus
Axiom-free topology of the polynomial lemniscate `Sₚ = {z : |p(z)| < 1}` for
`p ∈ UnitDiskPoly n`, built on the parent's root-factorization definitions.

## Status (S1, researcher-1, 2026-07-20) — Sₚ open / measurable / bounded
New file `proofs/Proofs/Erdos116WIP01.lean` (6 decls, 0 ax / 0 sorry,
host-verified `[propext, Classical.choice, Quot.sound]`). Discharges **Key lemma 1**
of problem.md: `continuous_eval`, `isOpen_sublevelSet`, `measurableSet_sublevelSet`,
`sublevelSet_subset_closedBall` (`Sₚ ⊆ closedBall 0 2`), `isBounded_sublevelSet`.

## Active Approach
Elementary complex-analysis / measure-theory scaffolding from the root product
`p(z) = ∏(z - zᵢ)`. The deep KLR `c/log n` lower bound and Pólya's `π` upper bound
rest on logarithmic potential theory absent from Mathlib and stay isolated.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- The KLR `c/log n` lower bound (and the `1/log n` vs `1/log log n` gap) is
  deep-blocked (route: logarithmic potential theory / value-distribution; reopen:
  materially new Mathlib potential-theory API required). Only the
  well-definedness/topology scaffolding is session-sized.

## Status (S4, researcher-1, 2026-07-22) — elementary layer SATURATED (stand-down)

The well-definedness / topology scaffolding is now **fully discharged** (all 0-axiom,
host-verified) across the earlier sessions and their merged PRs:
- **S1 (PR #40007)** `Sₚ` open / measurable / bounded (`Sₚ ⊆ closedBall 0 2`).
- **S2 (PR #40032)** finite 2D Lebesgue measure — the item the old "Next Action" below
  requested is DONE (`volume_sublevelSet_lt_top`, `volume_realProd_sublevelSet_lt_top` via the
  `ℂ ≅ ℝ²` volume-preserving equiv; `sublevelMeasure = volume.toReal` faithful).
- **S3 (PR #40898)** strict positivity (`volume_sublevelSet_pos`, `sublevelMeasure_pos`) — a
  nonempty open planar set has positive measure. So `0 < μ < ⊤`.

No session-sized elementary work remains: open/measurable/bounded/finite/positive are all
proven. The ONLY open content is DEEP and absent from Mathlib — the KLR `c/log n` lower bound,
Pólya's `π` upper bound, and the `1/log n` vs `1/log log n` gap (logarithmic potential theory /
lemniscate-area value distribution). These must be isolated as a single named assumption when
upgrading the gallery entry, not chased at the elementary layer. **STAND DOWN.**

## Next Action (SUPERSEDED — completed in S2, PR #40032)
~~Finiteness of `sublevelMeasure`: `Sₚ` is bounded + measurable ⟹ finite 2D
Lebesgue measure; bridge the parent's `ℝ×ℝ` sublevel set to `Sₚ ⊆ ℂ` via the
`ℂ ≅ ℝ²` measure isomorphism, then `measure_lt_top`.~~ Done. See S4 above: elementary
layer saturated; remaining work is deep potential theory (deep-blocked).
