# Knowledge Base: dissection-of-cubes-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Complete 2 geometric sorries in `proofs/Proofs/DissectionOfCubesOQ03.lean`:

1. **`smallest_above_is_smaller`** (line 390): If c is the floor-minimal cube (smallest
   side on its z-level) and does not reach the top, then any covering cube at the interior
   point directly above c has strictly smaller side than c.

2. **`global_min_not_reaching_top`** (line 469): The globally minimal cube in any
   valid all-different-sizes dissection with coverage cannot reach the top face.

Both theorems form the "descent chain" argument: there is always a smaller cube above any
non-top cube, making an infinite descent in a finite dissection impossible.

---

## Insights

### Proof Sketch for `smallest_above_is_smaller`
- The interior point `(px, py, c.z + c.side)` must be covered by some cube c' (via `CoversUnitCube`)
- c' is strictly above c's floor (z-level of c' > c.z, because PointInCube at c.z+c.side)
- Since c is the minimal-side cube on its own floor, any cube sharing c's floor has side ≥ c.side
- But c' is on a different floor: use `allDifferentSizes` to conclude c'.side < c.side
- Key Lean predicates to unfold: `CoversUnitCube`, `PointInCube`, `allDifferentSizes`

### Proof Sketch for `global_min_not_reaching_top`
- Assume for contradiction: c_min.z + c_min.side ≥ 1 (reaches top)
- c_min is not the floor-minimal if there is a smaller cube on the same floor -- but c_min is GLOBALLY minimal, so it IS the smallest everywhere
- Apply `smallest_above_is_smaller` to c_min: there must be a cube c' with c'.side < c_min.side
- This contradicts c_min being globally minimal → `global_min_not_reaching_top` holds
- NOTE: This theorem derives from `smallest_above_is_smaller` -- prove the latter first

### Dependency Order
- Prove `smallest_above_is_smaller` → derive `global_min_not_reaching_top` from it

---

## Key Definitions to Understand

- `CubeDissection`: record containing `cubes : Finset Cube` and coverage/disjointness axioms
- `CoversUnitCube d`: every interior point of the unit cube is in some cube of d
- `PointInCube px py pz c`: the point (px,py,pz) lies inside cube c (halfopen intervals)
- `allDifferentSizes d`: all cubes in d have distinct side lengths

---

## Dead Ends

[Approaches known not to work will be documented here]
