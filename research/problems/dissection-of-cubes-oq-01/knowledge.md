# Problem: Minimum number of repeated sizes needed in a cube dissection

## Problem Summary

**Open question**: Given that a cube cannot be dissected into finitely many cubes of all different sizes (Wiedijk #82), what is the minimum number of cubes that must participate in size collisions?

**Known facts**:
- Main theorem (Wiedijk #82): Any cube dissection must have ≥ 1 pair of same-size cubes
- Lower bound (proved here): Any nonempty cube dissection has ≥ 2 colliding cubes
- Open: Can exactly 2 cubes share a size? (HasMinimalCollision achievable?)

**Status**: PROGRESS — formalized OQ, proved lower bound

---

## Session 2026-02-21 (Session 1) - Initial Exploration and Formalization

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. **Investigated existing proof** (`DissectionOfCubes.lean`):
   - Found 4 axioms: 2 provable, 2 requiring geometric reasoning
   - `chain_length_bounded_axiom` → proved via `Fintype.card_le_of_injective`
   - `smallest_cube_top_is_floor_axiom` → proved via `Finset.exists_min_image`
   - `smaller_cube_above_axiom` → kept as axiom (requires 3D geometric covering)
   - `all_different_implies_long_chains_axiom` → kept as axiom (depends on above)

2. **Fixed bugs in DissectionOfCubes.lean**:
   - Removed `deriving Repr` (unsafe `Real.instRepr`)
   - Made `cubesTouchingBottom`/`cubesTouchingPlane` `noncomputable` (need classical `DecidablePred` for ℝ)

3. **Created `DissectionOfCubesOQ01.lean`**:
   - `IsCollisionPair d c₁ c₂`: two distinct cubes with same size
   - `sizeClass d c`: Finset of cubes with same size as c (classical, noncomputable)
   - `collidingCubes d`: Finset of cubes that share size with some other cube (noncomputable)
   - `every_dissection_has_collision`: proved from main theorem
   - `collision_class_at_least_two`: proved via `Finset.one_lt_card`
   - `at_least_two_colliding_cubes`: proved via `Finset.card_pair` and cardinality
   - `HasMinimalCollision d`: defined as `(collidingCubes d).card = 2`

### Key Findings

- Two proofs eliminated axiom status: `chain_length_bounded` and `smallest_cube_top_is_floor`
- Sorries reduced from 4 → 2 in the base proof
- Quantitative lower bound: `2 ≤ (collidingCubes d).card` for any nonempty dissection
- The geometric `covers_unit_cube : True` placeholder is the fundamental blocker for full proof

### Files Modified

- `proofs/Proofs/DissectionOfCubes.lean`: proved 2 axioms, fixed noncomputable issues
- `proofs/Proofs/DissectionOfCubesOQ01.lean`: new OQ formalization file (builds clean)
- `src/data/proofs/dissection-of-cubes/meta.json`: sorries updated 4→2
- `src/data/research/problems/dissection-of-cubes-oq-01.json`: knowledge updated

### Next Steps

1. Investigate if `HasMinimalCollision` is geometrically achievable
2. Try to prove `smaller_cube_above_axiom` using the formal disjointness conditions
3. Formalize volume identity: `∑ c.side³ = 1`
4. Consider submitting the remaining geometric axioms to Aristotle
