# Problem: Dissection of Cubes (Wiedijk #82)

**Slug**: dissection-of-cubes
**Created**: 2026-04-05T08:06:09-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{If a cube is partitioned into finitely many smaller cubes, at least two must have the same size.}
$$

Equivalently: there is no "squared cube" in 3D — no perfect dissection of a cube into finitely many cubes of mutually distinct sizes.

### Plain Language

Take a cube. Try to cut it up into smaller cubes where every piece has a different size. It's impossible. At least two of the smaller cubes must be the same size.

### Why This Matters

Wiedijk's Theorem #82. This is a classic impossibility result proved by Littlewood using infinite descent — one of the cleanest applications of well-foundedness in combinatorial geometry. The proof structure (smallest element on floor → smaller element above → infinite descent) is a paradigm for tiling impossibility arguments. In 2D, it IS possible to tile a square with unequal squares (a "perfect squared square" was first found in 1939).

## Known Results

### What's Already Proven (in DissectionOfCubes.lean)

- `CubeDissection` structure: formal model of a finite dissection
- `chain_length_bounded`: a strictly decreasing chain of cubes has length ≤ |dissection| (proved via `Fintype.card_le_of_injective`)
- `smallest_cube_top_is_floor`: the smallest cube on a floor exists (proved via `Finset.exists_min_image`)
- Complete proof of the main theorem given the two axioms

### What's Still Open (the 2 axioms)

- `smaller_cube_above_axiom`: For any cube c in a dissection with all-different sizes, if c is not at the top, there exists a cube c' with `c'.size < c.size`. This requires formalizing the 3D geometric argument: the smallest cube on any floor is surrounded by taller cubes, so its top face is covered by cubes from the dissection, all of which must be smaller.
- `all_different_implies_long_chains_axiom`: If all sizes differ, there exist arbitrarily long strictly decreasing chains. This follows from `smaller_cube_above_axiom` by induction.

### Our Goal

Prove `all_different_implies_long_chains_axiom` from `smaller_cube_above_axiom` (induction — likely feasible), then prove `smaller_cube_above_axiom` (geometric argument — harder but clear target). Reducing 2 axioms to 0 would make this a fully verified Wiedijk-100 theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| dissection-of-cubes | The parent gallery entry | Infinite descent |
| angle-trisection | Another impossibility proof (Galois theory) | Field extensions |
| borsuk-ulam | Topology impossibility | Covering spaces |

## Initial Thoughts

### Potential Approaches

1. **Prove axiom 2 from axiom 1 (easy)**
   - `all_different_implies_long_chains_axiom` follows by induction from `smaller_cube_above_axiom`
   - Start from any cube. By axiom 1, find a smaller cube above. Repeat n times.
   - Risk: Need to formalize the "not at top" condition propagating through the chain.

2. **Prove axiom 1 via geometric formalization (medium)**
   - Formalize 3D tiling: cubes cover the floor, the smallest floor-cube is surrounded by taller cubes, its top face is interior, and covered by dissection cubes.
   - Key: `CubeDissection.covers` ensures the top face of the smallest cube is covered.
   - Risk: 3D geometry in Lean is verbose. May need to axiomatize intermediate geometric lemmas.

3. **Replace geometry with a combinatorial model (alternative)**
   - Instead of formalizing 3D cubes, use a combinatorial abstraction: a valid cube dissection satisfies certain ordering properties.
   - Prove impossibility using well-foundedness of `<` on a Fintype.

### Key Difficulties

- 3D geometry in Lean/Mathlib is sparse. Covering arguments for unit cubes require showing that faces of one cube are covered by faces of others.
- The `CubeDissection` structure in the existing file uses `Finset Cube` — check if it has enough geometric content (covers, non-overlap conditions) to derive `smaller_cube_above_axiom`.

### What Would a Proof Need?

- The existing `CubeDissection` structure must encode that the dissection actually covers the unit cube and cubes don't overlap.
- A lemma: the bottom face is covered by cubes at z=0.
- A lemma: for the smallest such cube c, all cubes touching c's top face have size < c.size (since different sizes + c is smallest on floor).
- Mathlib: `Finset.exists_min_image`, `WellFounded`, `Fintype.card_le_of_injective` — already used.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The two axioms have clear proof sketches in the file header
- Axiom 2 from axiom 1 is a clean induction — likely provable in a single session
- Axiom 1 requires geometric content from the `CubeDissection` structure — depends on what's already formalized
- If the covering/non-overlap conditions are in the structure, axiom 1 may be provable in 1-2 sessions
- Similar impossibility proofs (angle-trisection, infinitude-of-primes) have been completed in the gallery

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 2-5 days
- If hard: unknown (may need stronger geometric infrastructure)

## References

### Papers
- Littlewood, J.E., "A Mathematician's Miscellany" (1953) — original proof sketch

### Online Resources
- Wiedijk's 100 Theorems: #82 Dissection of Cubes
- MathWorld: "Cube Dissection"

### Mathlib
- `Finset.exists_min_image` — finds minimum element of a finite set
- `WellFounded` — well-foundedness results
- `Fintype.card_le_of_injective` — already used in `chain_length_bounded`

## Metadata

```yaml
tags:
  - geometry
  - impossibility
  - infinite-descent
  - combinatorics
  - wiedijk-100
related_proofs:
  - dissection-of-cubes
  - angle-trisection
difficulty: medium
source: gallery-gap
created: 2026-04-05T08:06:09-07:00
```
