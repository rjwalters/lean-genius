import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Proofs.DissectionOfCubes

/-!
# Dissection of Cubes - Open Question 01

## Open Question

**Minimum number of cubes involved in size collisions in any cube dissection.**

Given that a cube cannot be dissected into finitely many cubes of all different sizes
(Wiedijk #82), we ask: **what is the minimum number of cubes that must participate
in "size collisions" (sharing their size with at least one other cube)?**

## Background

The main theorem (`DissectionOfCubes.dissection_of_cubes`) proves:
- No cube dissection can have all different sizes
- Equivalently: every dissection has ≥ 1 pair of same-size cubes

This file studies the quantitative version:
- **Lower bound** (proved here): every dissection has ≥ 2 cubes sharing some size
- **Trivial construction**: dissect into n³ equal cubes → exactly 1 distinct size
- **Open question**: Can a cube dissection have exactly 2 cubes of the same
  size and all remaining cubes of distinct sizes?

## Key Results

1. `every_dissection_has_collision` — every nonempty dissection has a collision pair
2. `collision_class_at_least_two` — the size class of a colliding cube has ≥ 2 members
3. `at_least_two_colliding_cubes` — quantitative lower bound: ≥ 2 cubes collide

## References

- `DissectionOfCubes.lean` — main impossibility theorem (Wiedijk #82)
- Freek Wiedijk, "Formalizing 100 Theorems", problem #82
- J.E. Littlewood, "A Mathematician's Miscellany" (1953)
-/

open DissectionOfCubes

namespace DissectionOfCubesOQ01

-- ============================================================
-- SECTION 1: Collision Pairs and Lower Bound
-- ============================================================

/-!
### Collision Pairs

A "collision pair" is a pair of distinct cubes sharing the same side length.
-/

/-- A collision pair: two distinct cubes in a dissection with the same size -/
def IsCollisionPair (d : CubeDissection) (c₁ c₂ : Cube) : Prop :=
  c₁ ∈ d.cubes ∧ c₂ ∈ d.cubes ∧ c₁ ≠ c₂ ∧ c₁.size = c₂.size

/-- **Lower Bound Theorem**: Every nonempty cube dissection has at least one collision pair.

    This follows directly from the main impossibility theorem (Wiedijk #82):
    since no dissection can have all different sizes, every dissection must
    have at least one pair of cubes sharing a size. -/
theorem every_dissection_has_collision (d : CubeDissection) (h_nonempty : d.cubes.Nonempty) :
    ∃ c₁ c₂ : Cube, IsCollisionPair d c₁ c₂ := by
  have h_not_all_diff := dissection_of_cubes d h_nonempty
  unfold CubeDissection.allDifferentSizes at h_not_all_diff
  push_neg at h_not_all_diff
  obtain ⟨c₁, hc₁, c₂, hc₂, hne, hsize⟩ := h_not_all_diff
  exact ⟨c₁, c₂, hc₁, hc₂, hne, hsize⟩

-- ============================================================
-- SECTION 2: Size Classes and Collision Count
-- ============================================================

/-!
### Size Classes

The "size class" of a cube c in dissection d is the set of all cubes in d
sharing the same side length as c.
-/

/-- The size class of a cube c in dissection d: all cubes with the same size.
    Classical decidability is used since equality of reals is not decidable constructively. -/
noncomputable def sizeClass (d : CubeDissection) (c : Cube) : Finset Cube :=
  haveI : DecidableEq Cube := Classical.decEq _
  d.cubes.filter (fun c' => c'.size = c.size)

/-- Every cube is in its own size class -/
theorem mem_sizeClass_self (d : CubeDissection) (c : Cube) (hc : c ∈ d.cubes) :
    c ∈ sizeClass d c := by
  unfold sizeClass
  haveI : DecidableEq Cube := Classical.decEq _
  simp [Finset.mem_filter, hc]

/-- A cube with a collision partner has size class of cardinality ≥ 2 -/
theorem collision_class_at_least_two (d : CubeDissection)
    (c : Cube) (hc : c ∈ d.cubes)
    (hcoll : ∃ c' : Cube, c' ∈ d.cubes ∧ c ≠ c' ∧ c.size = c'.size) :
    2 ≤ (sizeClass d c).card := by
  obtain ⟨c', hc'_mem, hne, hsize⟩ := hcoll
  unfold sizeClass
  haveI : DecidableEq Cube := Classical.decEq _
  apply Finset.one_lt_card.mpr
  refine ⟨c, ?_, c', ?_, hne⟩
  · simp [Finset.mem_filter, hc]
  · simp [Finset.mem_filter, hc'_mem, hsize]

-- ============================================================
-- SECTION 3: Quantitative Lower Bound
-- ============================================================

/-!
### At Least Two Cubes Collide

Every nonempty dissection must have at least 2 cubes participating in size collisions.
This is a strictly stronger statement than "there exists a collision pair" because it
says both cubes in the pair are distinct members of the dissection.
-/

/-- The set of cubes in a dissection that collide with some other cube -/
noncomputable def collidingCubes (d : CubeDissection) : Finset Cube :=
  haveI : DecidableEq Cube := Classical.decEq _
  d.cubes.filter (fun c => ∃ c' ∈ d.cubes, c ≠ c' ∧ c.size = c'.size)

/-- Every nonempty dissection has ≥ 2 colliding cubes -/
theorem at_least_two_colliding_cubes (d : CubeDissection) (h_nonempty : d.cubes.Nonempty) :
    2 ≤ (collidingCubes d).card := by
  haveI : DecidableEq Cube := Classical.decEq _
  obtain ⟨c₁, c₂, hc₁, hc₂, hne, hsize⟩ := every_dissection_has_collision d h_nonempty
  -- Both c₁ and c₂ are colliding
  have hc₁_coll : c₁ ∈ collidingCubes d := by
    unfold collidingCubes
    simp only [Finset.mem_filter]
    exact ⟨hc₁, c₂, hc₂, hne, hsize⟩
  have hc₂_coll : c₂ ∈ collidingCubes d := by
    unfold collidingCubes
    simp only [Finset.mem_filter]
    exact ⟨hc₂, c₁, hc₁, Ne.symm hne, hsize.symm⟩
  -- {c₁, c₂} ⊆ collidingCubes d, so card ≥ 2
  calc 2 = ({c₁, c₂} : Finset Cube).card := by
          rw [Finset.card_pair hne]
    _ ≤ (collidingCubes d).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hc₁_coll
          · exact hc₂_coll

-- ============================================================
-- SECTION 4: The Open Question - Minimal Collision
-- ============================================================

/-!
### The Open Question

Can a cube dissection have exactly 2 colliding cubes — one collision pair and
all others with distinct sizes?

**Formal statement**: Does there exist a valid cube dissection d such that
`(collidingCubes d).card = 2`?

**Status**: OPEN

We know:
- Lower bound: `(collidingCubes d).card ≥ 2` (proved above)
- Trivial upper bound: uniform dissections have ALL cubes colliding
- The interesting question: can we achieve exactly 2?
-/

/-- A dissection with "minimal collision": exactly 2 cubes share a size -/
def HasMinimalCollision (d : CubeDissection) : Prop :=
  (collidingCubes d).card = 2

/-!
**OPEN QUESTION**: `∃ d : CubeDissection, d.cubes.Nonempty ∧ HasMinimalCollision d`

The difficulty is that the geometric covering constraint (`covers_unit_cube`) is
currently a placeholder (`True`) in our formalization. A genuine construction would
need to verify that the cubes actually tile the unit cube.

**Volume constraint** (informal): any dissection must satisfy
  ∑_{c ∈ d.cubes} c.side³ = 1

For 2 cubes of size s and n-2 cubes of distinct sizes s₁,...,s_{n-2}:
  2s³ + s₁³ + ... + s_{n-2}³ = 1

Whether this can be achieved with a valid geometric tiling is the open question.
-/

-- ============================================================
-- SECTION 5: Connection to Infinite Descent
-- ============================================================

/-!
### Why the Floor Argument Forces Repeats

Littlewood's infinite descent argument shows that the repeats arise from a
geometric cascade:

1. The smallest cube C₀ touching the bottom floor must be surrounded by taller cubes
2. C₀'s top face becomes a new floor, covered by smaller cubes
3. The smallest of these, C₁, creates another floor above it
4. This cascades: C₀ > C₁ > C₂ > ... in size

This cascade forces multiple "floors" of different heights, and the cubes at each
level must collectively tile the corresponding horizontal cross-section. The
geometric constraints typically force many size repetitions in practice.

Whether a near-perfect dissection (only 2 colliding cubes) is geometrically
realizable, or whether the cascade forces many more, is the key open question.
-/

/-- The floor argument: contradiction from all-different-sizes (restated from main file) -/
theorem impossible_all_different (d : CubeDissection) (h : d.cubes.Nonempty) :
    ¬ d.allDifferentSizes :=
  dissection_of_cubes d h

-- ============================================================
-- SECTION 6: Comparison with 2D (Squared Squares)
-- ============================================================

/-!
### Contrast with Squaring the Square

In 2D, "squared squares" exist: a square can be tiled with smaller squares of ALL
different sizes. The smallest simple perfect squared square has 21 squares.

This shows that dimension matters fundamentally:
- **2D**: Perfect tiling (all different sizes) exists
- **3D**: Perfect tiling is IMPOSSIBLE (Wiedijk #82)

The question here is about the "almost perfect" version in 3D: how close to
perfect can we get? Can we achieve exactly 1 repeated size? This is the open question.

The 2D analog of our open question would be: "What is the minimum number of
colliding squares in a squared rectangle?" For rectangles (which cannot be
perfectly squared), this question has been studied but may not be fully resolved.
-/

-- ============================================================
-- SECTION 7: Summary
-- ============================================================

/-!
## Summary of Results

### Proved in This Session

| Result | Status | Method |
|--------|--------|--------|
| Every nonempty dissection has ≥ 1 collision pair | ✓ | From Wiedijk #82 |
| Every nonempty dissection has ≥ 2 colliding cubes | ✓ | Pair extraction + cardinality |
| `chain_length_bounded`: injective chain bound | ✓ | In DissectionOfCubes.lean |
| `smallest_cube_top_is_floor`: min size exists | ✓ | In DissectionOfCubes.lean |

### Open Questions

| Question | Status |
|----------|--------|
| Can a dissection have exactly 2 colliding cubes? | OPEN |
| What is min card of `collidingCubes d`? | OPEN (lower bound: 2) |
| Geometric covering formalization | Partial (placeholder) |

### Remaining Axioms in Base Proof

`DissectionOfCubes.lean` still has 2 axioms requiring 3D geometric formalization:
- `smaller_cube_above_axiom`: smallest cube on floor has smaller cubes above
- `all_different_implies_long_chains_axiom`: chains of decreasing sizes are arbitrarily long
-/

end DissectionOfCubesOQ01
