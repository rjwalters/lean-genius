# Research State: minkowski-theorem-oq-02-oq-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-04-05
**Iteration**: 2

## Current Focus

Eliminate three measure-theoretic axioms from `MinkowskiTheoremOQ02.lean`. Start with
measurability (open set argument), then convexity (halfspace intersection), then volume
(shear map change-of-variables).

## Active Approach

Three-axiom elimination strategy (easiest first):

1. **dirichletSet_measurable** (EASY): Set is open — preimage of `Ioo × Ioo` under
   the continuous map `v ↦ (v 0, α * v 0 - v 1)`. Apply `IsOpen.measurableSet`.

2. **dirichletSet_convex** (EASY): Intersection of halfspaces. Use `Convex.inter`
   with `convex_Ioo` or `convex_halfspace_lt`.

3. **dirichletSet_volume** (HARDER): Shear T(x,y)=(x,αx-y) with |det T|=1.
   S = T⁻¹(R), vol(R) = 2(Q+1)·(2/Q) = 4(Q+1)/Q. Use change-of-variables or Fubini.

## Key Mathlib Lemmas to Explore

- `Convex.inter`, `convex_Ioo`, `convex_halfspace_lt`
- `IsOpen.measurableSet`, `IsOpen.preimage`, `continuous_id`
- `Real.volume_Ioo`, `MeasureTheory.volume_pi_Ioo`
- `MeasureTheory.Measure.map_linearMap`

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action

1. Open `proofs/Proofs/MinkowskiTheoremOQ02.lean` and read the three axiom declarations
2. Try `dirichletSet_measurable` first: show set is open via continuous preimage of Ioo
3. Then attempt `dirichletSet_convex` via Convex.inter decomposition
