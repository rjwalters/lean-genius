import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Proofs.DissectionOfCubesOQ01

/-!
# Dissection of Cubes — OQ01, Sub-question 01

## Question

Is `HasMinimalCollision` achievable? Can a cube dissection have **exactly 2 colliding cubes**?

## Answer

**Yes** — within our formalization, we construct an explicit `CubeDissection d` with
`(collidingCubes d).card = 2`.

## Construction

Three axis-aligned cubes inside the unit cube:

| Cube | Corner | Side | Size role |
|------|--------|------|-----------|
| A | (0, 0, 0) | 1/4 | collision pair |
| B | (1/2, 0, 0) | 1/4 | collision pair |
| C | (0, 0, 1/2) | 1/3 | unique size — does NOT collide |

A and B share size 1/4, so both are in `collidingCubes`. C has distinct size 1/3, so C
is not in `collidingCubes`. Hence `(collidingCubes d).card = |{A, B}| = 2`.

## Caveat

Our `CubeDissection` structure has `covers_unit_cube : True` as a placeholder — the
full geometric covering constraint is not formalized. This proof shows that achievability
is **not obstructed by the combinatorial constraints** (containment + pairwise disjointness
alone). Whether a genuine tiling of the unit cube can achieve this minimum remains an
open geometric question.

## Mathematical Insight

The proof separates two aspects of the open question:
- **Combinatorial**: Can 3+ pairwise-disjoint cubes, all inside the unit cube, have
  exactly one repeated size? ✓ (proved here)
- **Geometric/volumetric**: Can such a configuration also perfectly tile the unit cube?
  ✗ (not addressed — still open)
-/

open DissectionOfCubes
open DissectionOfCubesOQ01

namespace DissectionOfCubesOQ01OQ01

-- ============================================================
-- SECTION 1: Concrete Cube Definitions
-- ============================================================

/-- Cube A: corner (0, 0, 0), side 1/4 -/
noncomputable def cubeA : Cube := ⟨0, 0, 0, 1/4, by norm_num⟩

/-- Cube B: corner (1/2, 0, 0), side 1/4 — same size as A, forming the collision pair -/
noncomputable def cubeB : Cube := ⟨1/2, 0, 0, 1/4, by norm_num⟩

/-- Cube C: corner (0, 0, 1/2), side 1/3 — unique size, does not collide -/
noncomputable def cubeC : Cube := ⟨0, 0, 1/2, 1/3, by norm_num⟩

-- Sizes reduce by definition
@[simp] lemma cubeA_size : cubeA.size = 1/4 := rfl
@[simp] lemma cubeB_size : cubeB.size = 1/4 := rfl
@[simp] lemma cubeC_size : cubeC.size = 1/3 := rfl

/-- A and B share the same size -/
lemma cubeAB_same_size : cubeA.size = cubeB.size := by simp

/-- C has a different size from A -/
lemma cubeC_size_ne_cubeA : cubeC.size ≠ cubeA.size := by
  simp; norm_num

/-- C has a different size from B -/
lemma cubeC_size_ne_cubeB : cubeC.size ≠ cubeB.size := by
  simp; norm_num

-- ============================================================
-- SECTION 2: Cube Distinctness
-- ============================================================

/-- A ≠ B: they differ in x-coordinate -/
lemma cubeA_ne_cubeB : cubeA ≠ cubeB := by
  intro h
  have hx : cubeA.x = cubeB.x := congr_arg Cube.x h
  simp only [cubeA, cubeB] at hx
  norm_num at hx

/-- A ≠ C: they differ in side length -/
lemma cubeA_ne_cubeC : cubeA ≠ cubeC := by
  intro h
  have hs : cubeA.side = cubeC.side := congr_arg Cube.side h
  simp only [cubeA, cubeC] at hs
  norm_num at hs

/-- B ≠ C: they differ in side length -/
lemma cubeB_ne_cubeC : cubeB ≠ cubeC := by
  intro h
  have hs : cubeB.side = cubeC.side := congr_arg Cube.side h
  simp only [cubeB, cubeC] at hs
  norm_num at hs

-- ============================================================
-- SECTION 3: Containment in Unit Cube
-- ============================================================

/-- A lies in [0,1]³ -/
lemma cubeA_inUnitCube : cubeA.inUnitCube := by
  unfold Cube.inUnitCube cubeA
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- B lies in [0,1]³ -/
lemma cubeB_inUnitCube : cubeB.inUnitCube := by
  unfold Cube.inUnitCube cubeB
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- C lies in [0,1]³  (C.z + C.side = 1/2 + 1/3 = 5/6 ≤ 1) -/
lemma cubeC_inUnitCube : cubeC.inUnitCube := by
  unfold Cube.inUnitCube cubeC
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ============================================================
-- SECTION 4: Pairwise Interior Disjointness
-- ============================================================
-- Disjointness is witnessed by coordinate separation:
--   A vs B: A.x + A.side = 1/4 ≤ 1/2 = B.x  (x-separated)
--   A vs C: A.z + A.side = 1/4 ≤ 1/2 = C.z  (z-separated)
--   B vs C: B.z + B.side = 1/4 ≤ 1/2 = C.z  (z-separated)

/-- A and B are interior-disjoint (x-separated: A.x + 1/4 ≤ B.x) -/
lemma cubeA_cubeB_disjoint : cubeA.interiorDisjoint cubeB := by
  unfold Cube.interiorDisjoint cubeA cubeB
  left; norm_num

/-- B and A are interior-disjoint (symmetric: A.x + A.side ≤ B.x gives 2nd disjunct) -/
lemma cubeB_cubeA_disjoint : cubeB.interiorDisjoint cubeA := by
  unfold Cube.interiorDisjoint cubeA cubeB
  right; left; norm_num

/-- A and C are interior-disjoint (z-separated: A.z + 1/4 ≤ C.z) -/
lemma cubeA_cubeC_disjoint : cubeA.interiorDisjoint cubeC := by
  unfold Cube.interiorDisjoint cubeA cubeC
  right; right; right; right; left; norm_num

/-- C and A are interior-disjoint (symmetric: A.z + A.side ≤ C.z gives 6th disjunct) -/
lemma cubeC_cubeA_disjoint : cubeC.interiorDisjoint cubeA := by
  unfold Cube.interiorDisjoint cubeC cubeA
  right; right; right; right; right; norm_num

/-- B and C are interior-disjoint (z-separated: B.z + 1/4 ≤ C.z) -/
lemma cubeB_cubeC_disjoint : cubeB.interiorDisjoint cubeC := by
  unfold Cube.interiorDisjoint cubeB cubeC
  right; right; right; right; left; norm_num

/-- C and B are interior-disjoint (symmetric: B.z + B.side ≤ C.z gives 6th disjunct) -/
lemma cubeC_cubeB_disjoint : cubeC.interiorDisjoint cubeB := by
  unfold Cube.interiorDisjoint cubeC cubeB
  right; right; right; right; right; norm_num

-- ============================================================
-- SECTION 5: The Example Dissection
-- ============================================================

/-- The finite set of our three example cubes -/
noncomputable def exampleCubes : Finset Cube :=
  haveI : DecidableEq Cube := Classical.decEq _
  {cubeA, cubeB, cubeC}

/-- The example CubeDissection — covers_unit_cube holds trivially -/
noncomputable def exampleDissection : CubeDissection where
  cubes := exampleCubes
  all_contained := by
    intro c hc
    haveI : DecidableEq Cube := Classical.decEq _
    simp only [exampleCubes, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact cubeA_inUnitCube
    · exact cubeB_inUnitCube
    · exact cubeC_inUnitCube
  pairwise_disjoint := by
    intro c₁ hc₁ c₂ hc₂ hne
    haveI : DecidableEq Cube := Classical.decEq _
    simp only [exampleCubes, Finset.mem_insert, Finset.mem_singleton] at hc₁ hc₂
    rcases hc₁ with rfl | rfl | rfl <;> rcases hc₂ with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact cubeA_cubeB_disjoint
    · exact cubeA_cubeC_disjoint
    · exact cubeB_cubeA_disjoint
    · exact absurd rfl hne
    · exact cubeB_cubeC_disjoint
    · exact cubeC_cubeA_disjoint
    · exact cubeC_cubeB_disjoint
    · exact absurd rfl hne
  covers_unit_cube := trivial

-- ============================================================
-- SECTION 6: Membership Facts
-- ============================================================

lemma cubeA_mem : cubeA ∈ exampleDissection.cubes := by
  haveI : DecidableEq Cube := Classical.decEq _
  simp [exampleDissection, exampleCubes]

lemma cubeB_mem : cubeB ∈ exampleDissection.cubes := by
  haveI : DecidableEq Cube := Classical.decEq _
  simp [exampleDissection, exampleCubes, Finset.mem_insert, Finset.mem_singleton,
        cubeA_ne_cubeB.symm]

lemma cubeC_mem : cubeC ∈ exampleDissection.cubes := by
  haveI : DecidableEq Cube := Classical.decEq _
  simp [exampleDissection, exampleCubes, Finset.mem_insert, Finset.mem_singleton,
        cubeA_ne_cubeC.symm, cubeB_ne_cubeC.symm]

/-- Helper: membership in collidingCubes via filter -/
lemma mem_collidingCubes_iff (c : Cube) :
    c ∈ collidingCubes exampleDissection ↔
      c ∈ exampleDissection.cubes ∧
        ∃ c' ∈ exampleDissection.cubes, c ≠ c' ∧ c.size = c'.size := by
  haveI : DecidableEq Cube := Classical.decEq _
  simp [collidingCubes, Finset.mem_filter]

-- ============================================================
-- SECTION 7: Which Cubes Collide
-- ============================================================

/-- A collides: B is in the dissection with A ≠ B and equal size -/
lemma cubeA_collides : cubeA ∈ collidingCubes exampleDissection := by
  rw [mem_collidingCubes_iff]
  exact ⟨cubeA_mem, cubeB, cubeB_mem, cubeA_ne_cubeB, cubeAB_same_size⟩

/-- B collides: A is in the dissection with B ≠ A and equal size -/
lemma cubeB_collides : cubeB ∈ collidingCubes exampleDissection := by
  rw [mem_collidingCubes_iff]
  exact ⟨cubeB_mem, cubeA, cubeA_mem, cubeA_ne_cubeB.symm, cubeAB_same_size.symm⟩

/-- C does NOT collide: its size 1/3 differs from every other cube's size -/
lemma cubeC_not_collides : cubeC ∉ collidingCubes exampleDissection := by
  haveI : DecidableEq Cube := Classical.decEq _
  rw [mem_collidingCubes_iff]
  push_neg
  intro _
  -- Must show: for every c' in {A, B, C}, either cubeC = c' or cubeC.size ≠ c'.size
  intro c' hc'
  simp only [exampleDissection, exampleCubes, Finset.mem_insert, Finset.mem_singleton] at hc'
  rcases hc' with rfl | rfl | rfl
  · -- c' = cubeA: sizes differ (1/3 ≠ 1/4)
    right; simp; norm_num
  · -- c' = cubeB: sizes differ (1/3 ≠ 1/4)
    right; simp; norm_num
  · -- c' = cubeC: same cube, so ¬(cubeC ≠ cubeC)
    left; rfl

-- ============================================================
-- SECTION 8: Colliding Cubes = {A, B}
-- ============================================================

/-- The colliding cubes of the example dissection are exactly {cubeA, cubeB} -/
theorem colliding_eq_pair :
    collidingCubes exampleDissection = {cubeA, cubeB} := by
  haveI : DecidableEq Cube := Classical.decEq _
  ext c
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hc
    -- c ∈ collidingCubes ⊆ exampleDissection.cubes = {A, B, C}
    have hmem : c ∈ exampleDissection.cubes := (mem_collidingCubes_iff c).mp hc |>.1
    simp only [exampleDissection, exampleCubes, Finset.mem_insert,
               Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · left; rfl
    · right; rfl
    · exact absurd hc cubeC_not_collides
  · rintro (rfl | rfl)
    · exact cubeA_collides
    · exact cubeB_collides

-- ============================================================
-- SECTION 9: Main Results
-- ============================================================

/-- **Theorem**: The example dissection has exactly 2 colliding cubes -/
theorem example_has_minimal_collision : HasMinimalCollision exampleDissection := by
  unfold HasMinimalCollision
  haveI : DecidableEq Cube := Classical.decEq _
  rw [colliding_eq_pair, Finset.card_pair cubeA_ne_cubeB]

/-- **Main Result**: `HasMinimalCollision` is achievable in our formalization.
    There exists a `CubeDissection` with a nonempty cube set and exactly 2 colliding cubes.

    Note: this proves achievability under the current formalization where
    `covers_unit_cube : True`. Whether a genuine geometric tiling can achieve
    this minimum remains an open question. -/
theorem minimal_collision_achievable :
    ∃ d : CubeDissection, d.cubes.Nonempty ∧ HasMinimalCollision d :=
  ⟨exampleDissection, ⟨cubeA, cubeA_mem⟩, example_has_minimal_collision⟩

-- ============================================================
-- SECTION 10: Connection to the Lower Bound
-- ============================================================

/-!
### Tightness of the Lower Bound

`DissectionOfCubesOQ01.at_least_two_colliding_cubes` proved that every nonempty
dissection has `(collidingCubes d).card ≥ 2`.

`minimal_collision_achievable` shows the bound **2 is tight** in our formalization:
the lower bound is exactly achieved.

The open geometric question is whether this can be achieved with `covers_unit_cube`
replaced by an actual covering predicate. Littlewood's cascade argument suggests
that geometric constraints may force strictly more than 2 colliding cubes, but this
has not been proved.
-/

/-- The lower bound 2 is achievable: there exists a dissection achieving the minimum -/
theorem lower_bound_tight :
    ∃ d : CubeDissection, d.cubes.Nonempty ∧
      (collidingCubes d).card = 2 ∧
      2 ≤ (collidingCubes d).card := by
  obtain ⟨d, hne, hmin⟩ := minimal_collision_achievable
  exact ⟨d, hne, hmin, le_of_eq hmin.symm⟩

end DissectionOfCubesOQ01OQ01
