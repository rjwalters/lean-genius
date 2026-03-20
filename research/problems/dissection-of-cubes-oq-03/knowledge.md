# Dissection of Cubes OQ-03: Connections to Packing Problems

## Problem
Formalize geometric covering axiom without external axioms.

## Status: PROGRESS (2 sorries, 2 axioms remaining)

### Previous State
- 0 sorries, 3 axioms (packing_volume_bound, dissection_volume_exact, debruijn_brick_tiling)
- Pre-existing compilation errors (namespace issues)
- `debruijn_brick_tiling` axiom had unsound `↔ True` formulation

### Current State (after this session)
- **Fixed** all compilation errors (namespace resolution for dot notation)
- **Replaced** unsound `debruijn_brick_tiling` with proper `CanTileWithBrick` formulation
- **Proved** forward direction `aligned_divisibility_implies_tiling`
- **Proved** special case `cube_tiled_by_smaller_cubes`
- **Formalized** `CoversUnitCube` — proper geometric coverage predicate
- **Proved** `floor_coverage` and `bottom_floor_nonempty` from coverage
- **Stated** `smallest_above_is_smaller` — isolates the key geometric claim (sorry)
- **Proved** `dissection_of_cubes_from_coverage` — alternative main theorem from coverage

### Key Insights

1. **The coverage condition** `covers_unit_cube : True` in the base file was the fundamental gap.
   Replacing it with `CoversUnitCube` (every point in [0,1]³ covered by some cube) enables
   deriving the descent argument without external axioms.

2. **The de Bruijn axiom was unsound**: `deBruijnCondition container brick ↔ True` asserts
   every container-brick pair satisfies the divisibility condition, which is false
   (e.g., 1×1×1 cube cannot be tiled by 2×2×2 bricks).

3. **Namespace issues** caused the pre-existing code not to compile. Definitions extending
   `DissectionOfCubes.Cube` and `DissectionOfCubes.CubeDissection` must be in the
   `DissectionOfCubes` namespace for Lean 4 dot notation to resolve correctly.

4. **The geometric content reduces to one claim**: `smallest_above_is_smaller` —
   if a cube c is the smallest on its floor and doesn't reach the top, then any cube
   covering an interior point on c's top face must be strictly smaller. This is the
   heart of Littlewood's infinite descent argument.

### Axiom/Sorry Inventory

| Item | Status | Type |
|------|--------|------|
| `packing_volume_bound` | axiom (unchanged) | Needs measure theory |
| `dissection_volume_exact` | axiom (unchanged) | Needs measure theory |
| `debruijn_brick_tiling` | **REMOVED** (was unsound) | Replaced with proved formulation |
| `smallest_above_is_smaller` | sorry (NEW) | Geometric confinement |
| `descent_chains_from_coverage` | sorry (NEW) | Induction from above |

### Net Change
- **Axioms**: 3 → 2 (removed unsound de Bruijn)
- **Sorries**: 0 → 2 (new, well-scoped geometric claims)
- **Compilation**: broken → working
- **Theorems proved**: +5 (floor_coverage, bottom_floor_nonempty, aligned_divisibility_implies_tiling, cube_tiled_by_smaller_cubes, dissection_of_cubes_from_coverage)

## Approaches Explored

### Coverage formalization + axiom elimination
**Status**: succeeded (partial)
Formalized CoversUnitCube, proved bottom_floor_nonempty and floor_coverage,
stated smallest_above_is_smaller with clear geometric hypotheses.

### Pre-existing code repair
**Status**: succeeded
Fixed namespace issues preventing compilation. Moved Cube.volume and
CubeDissection.toPacking to DissectionOfCubes namespace.

### de Bruijn correction
**Status**: succeeded
Replaced unsound `↔ True` with proper `CanTileWithBrick` predicate.
Proved forward direction and cube special case.

## Next Steps
1. Prove `smallest_above_is_smaller` — needs 2D tiling argument showing
   cubes on the top face of the smallest floor cube are geometrically confined
2. Prove `descent_chains_from_coverage` — induction using `smallest_above_is_smaller`
3. Volume axioms may be provable via Mathlib's `MeasureTheory.MeasurableSet`
