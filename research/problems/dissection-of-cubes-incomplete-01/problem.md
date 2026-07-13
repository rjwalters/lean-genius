# Problem: Complete Geometric Sorries in Dissection of Cubes OQ03

**Slug**: dissection-of-cubes-incomplete-01
**Created**: 2026-03-23T17:46:34.541Z
**Updated**: 2026-04-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Two geometric sorries remain in `proofs/Proofs/DissectionOfCubesOQ03.lean`. The file
explores connections between cube dissection impossibility and packing problems, building
toward a machine-checked version of the classical impossibility result.

The two sorry-tagged theorems are:

1. **`smallest_above_is_smaller`** (line 390): If c is the smallest cube on its floor
   (z-level) in a valid dissection with all-different sizes, and c does not reach the top,
   then there exists a strictly smaller cube above it at a given interior point.

2. **`global_min_not_reaching_top`** (line 469): The globally minimal cube in a valid
   all-different-sizes dissection with coverage cannot reach the top face.

### Formal Statements

```lean
theorem smallest_above_is_smaller (d : CubeDissection) (h_diff : d.allDifferentSizes)
    (hcov : CoversUnitCube d) (c : Cube) (hc : c ∈ d.cubes)
    (h_smallest_on_floor : ∀ c' ∈ d.cubes, c'.z = c.z → c.side ≤ c'.side)
    (h_not_top : c.z + c.side < 1)
    (px py : ℝ) (hpx : c.x < px ∧ px < c.x + c.side)
    (hpy : c.y < py ∧ py < c.y + c.side) :
    ∃ c' ∈ d.cubes, PointInCube px py (c.z + c.side) c' ∧ c'.side < c.side

theorem global_min_not_reaching_top (d : CubeDissection) (h_diff : d.allDifferentSizes)
    (hcov : CoversUnitCube d) (h_nonempty : d.cubes.Nonempty)
    (c_min : Cube) (hc_min_mem : c_min ∈ d.cubes)
    (hc_min_le : ∀ c' ∈ d.cubes, c_min.side ≤ c'.side) :
    c_min.z + c_min.side < 1
```

### Why This Matters

These two lemmas are the geometric core of the cube dissection impossibility argument.
Together they establish the "descent chain" property: in any valid dissection with
all-different sizes, one can always find an infinite descending sequence of cube sizes,
contradicting finiteness. Completing these sorries would:
1. Make `DissectionOfCubesOQ03.lean` sorry-free
2. Strengthen the gallery with fully verified geometric support lemmas
3. Advance toward a machine-checked proof of the classical cube dissection theorem

## Classification

```yaml
tier: A
significance: 7
tractability: 6
tags:
  - seeker-selected
  - geometry
  - completion
  - wiedijk-100
  - sorry-completion
```

**Significance**: 7/10
**Tractability**: 6/10

## Known Results

### What's Already Proven in the File

- `DissectionOfCubes.lean`: Core axiomatization (0 sorries)
- `DissectionOfCubesOQ03.lean`:
  - Volume bounds for packings (proved)
  - Dissection-packing bridge theorem (proved)
  - `descent_chains_from_coverage`: proved from `exists_smaller_cube`
  - `exists_smaller_cube`: follows from `smallest_above_is_smaller` (still sorry)

### What's Still Open

- The two sorry theorems above (geometric confinement arguments)

### Our Goal

Prove `smallest_above_is_smaller` and `global_min_not_reaching_top` in Lean 4, using
Mathlib's real number and geometric machinery.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| dissection-of-cubes | Base proof, CubeDissection structure | Axiomatization of coverage |
| dissection-of-cubes-oq-01 | First OQ: extension results | Finset reasoning |
| dissection-of-cubes-oq-02 | Second OQ: tiling/periodicity | |
| dissection-of-cubes-oq-03 | Same file being completed | Geometric confinement |

## Initial Thoughts

### Potential Approaches

1. **Coverage + Interval Analysis**: Use `CoversUnitCube` to extract a cube covering the
   interior point `(px, py, c.z + c.side)`. Since any such cube must be on a strictly
   higher z-level than c, and c is minimal on its floor, the covering cube has smaller side.

2. **Global Minimum Contradiction**: For `global_min_not_reaching_top`, if c_min reaches
   the top (c_min.z + c_min.side ≥ 1), the point just above it would need coverage from
   a cube smaller than c_min (by the floor argument), contradicting global minimality.

3. **Read definitions first**: Understanding the exact predicates `CoversUnitCube`,
   `PointInCube`, and `allDifferentSizes` is the critical first step.

### Key Difficulties

- `CoversUnitCube` definition: what exactly does it expose for proof use?
- `PointInCube` predicate: exact halfopen/closed interval structure?
- Using `allDifferentSizes` to derive strict inequality on cube sides

### What Would a Proof Need?

- Full understanding of `CubeDissection`, `CoversUnitCube`, `PointInCube` definitions in DissectionOfCubes.lean
- Key step: covering cube at `c.z + c.side` must be on a different z-level → smaller side via all-different-sizes

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- Mathematical argument is clear (geometric confinement)
- Lean difficulty: unpacking `CoversUnitCube` and `PointInCube` definitions
- Once structure understood, `linarith` and `Finset` lemmas should close arithmetic

## References

### Papers
- Brooks, Smith, Stone, Tutte, "The Dissection of Rectangles into Squares" (1940)
- Dehn (1903) — foundational geometric impossibility work

### Lean Files
- `proofs/Proofs/DissectionOfCubes.lean` — core definitions and axioms
- `proofs/Proofs/DissectionOfCubesOQ03.lean` — file with the 2 sorries (lines 390, 469)

## Metadata

```yaml
tags:
  - geometry
  - cube-dissection
  - completion
  - wiedijk-100
  - sorry-completion
related_proofs:
  - dissection-of-cubes
  - dissection-of-cubes-oq-03
difficulty: medium-high
source: gallery-gap
created: 2026-03-23T17:46:34.541Z
updated: 2026-04-02
```
