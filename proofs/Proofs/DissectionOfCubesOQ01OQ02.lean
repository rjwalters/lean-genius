import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Proofs.DissectionOfCubesOQ01
import Proofs.DissectionOfCubesOQ01OQ01

/-!
# Dissection of Cubes — OQ01, Sub-question 02

## Question

> **What is the actual minimum of `collidingCubes.card` over all valid dissections?**

(Parent open question `DissectionOfCubesOQ01`, item 2.)

## Answer

**Exactly 2.**  Within the combinatorial formalization, the set of attainable
collision counts has a least element, and that least element is `2`.

This packages the two facts proved separately in the sibling files into the
canonical order-theoretic statement that pins down the minimum:

- **Lower bound** (`DissectionOfCubesOQ01.at_least_two_colliding_cubes`):
  every nonempty dissection has `(collidingCubes d).card ≥ 2`.
- **Achievability** (`DissectionOfCubesOQ01OQ01.example_has_minimal_collision`):
  there is a nonempty dissection with `(collidingCubes d).card = 2`.

Together these say `IsLeast collisionSpectrum 2`, equivalently
`sInf collisionSpectrum = 2`, and in particular `0` and `1` are **not**
attainable.

## A genuine spectrum, not a singleton

To show the minimum `2` is the bottom of a *nontrivial* attainable set — rather
than the only attainable value — we also exhibit a dissection with **three**
colliding cubes (three equal-size cubes side-by-side), giving
`3 ∈ collisionSpectrum`.  So the spectrum contains at least `{2, 3}` and the
"minimum" is a real boundary.

## Caveat

As in the sibling files, the `CubeDissection` structure carries
`covers_unit_cube : True` as a placeholder for the full 3D tiling constraint.
Every statement here is therefore about the **combinatorial** model (containment
+ pairwise interior-disjointness).  Whether the genuine geometric minimum is
also `2`, or whether Littlewood's cascade forces strictly more, remains open.
-/

open DissectionOfCubes
open DissectionOfCubesOQ01
open DissectionOfCubesOQ01OQ01

namespace DissectionOfCubesOQ01OQ02

-- ============================================================
-- SECTION 1: The Collision Spectrum
-- ============================================================

/-- The **collision spectrum**: the set of all collision counts attainable by a
    nonempty cube dissection.  An element `n` means "some nonempty dissection has
    exactly `n` colliding cubes". -/
def collisionSpectrum : Set ℕ :=
  { n | ∃ d : CubeDissection, d.cubes.Nonempty ∧ (collidingCubes d).card = n }

/-- `2` is attainable: the explicit `exampleDissection` of OQ01-OQ01 realizes it. -/
theorem two_mem_collisionSpectrum : 2 ∈ collisionSpectrum :=
  ⟨exampleDissection, ⟨cubeA, cubeA_mem⟩, example_has_minimal_collision⟩

/-- Every attainable collision count is `≥ 2` (the OQ01 lower bound). -/
theorem collisionSpectrum_lower_bound : ∀ n ∈ collisionSpectrum, 2 ≤ n := by
  rintro n ⟨d, hne, rfl⟩
  exact at_least_two_colliding_cubes d hne

-- ============================================================
-- SECTION 2: The Minimum is Exactly 2
-- ============================================================

/-- **Main theorem.**  `2` is the least element of the collision spectrum:
    it is attainable and it lower-bounds every attainable value.

    This is the precise answer to the parent open question
    *"What is the actual minimum of `collidingCubes.card`?"* — within the
    combinatorial model, the minimum is exactly `2`. -/
theorem isLeast_collisionSpectrum : IsLeast collisionSpectrum 2 :=
  ⟨two_mem_collisionSpectrum, collisionSpectrum_lower_bound⟩

/-- Restatement via `sInf`: the infimum of the collision spectrum is `2`. -/
theorem sInf_collisionSpectrum : sInf collisionSpectrum = 2 :=
  isLeast_collisionSpectrum.csInf_eq

/-- The minimum collision count, stated directly: there is a nonempty dissection
    attaining `2`, and no nonempty dissection attains anything smaller. -/
theorem minimum_collision_count_is_two :
    (∃ d : CubeDissection, d.cubes.Nonempty ∧ (collidingCubes d).card = 2) ∧
    (∀ d : CubeDissection, d.cubes.Nonempty → 2 ≤ (collidingCubes d).card) := by
  refine ⟨two_mem_collisionSpectrum, ?_⟩
  intro d hne
  exact at_least_two_colliding_cubes d hne

/-- `0` colliding cubes is impossible for a nonempty dissection. -/
theorem zero_not_mem_collisionSpectrum : 0 ∉ collisionSpectrum := by
  intro h
  have := collisionSpectrum_lower_bound 0 h
  omega

/-- A single colliding cube is impossible: collisions come in (at least) pairs. -/
theorem one_not_mem_collisionSpectrum : 1 ∉ collisionSpectrum := by
  intro h
  have := collisionSpectrum_lower_bound 1 h
  omega

-- ============================================================
-- SECTION 3: A Third Witness — The Spectrum is Nontrivial
-- ============================================================

/-!
We now show the minimum `2` sits at the bottom of a genuine spectrum by
exhibiting a dissection with **three** colliding cubes.

Three equal-size cubes (side `1/4`) placed side-by-side along the x-axis at
`x = 0, 1/4, 1/2`.  All three share the size `1/4`, so all three collide.

We reuse `cubeA` (x = 0) and `cubeB` (x = 1/2) from OQ01-OQ01 and add `cubeD`
at `x = 1/4`.
-/

/-- Cube D: corner `(1/4, 0, 0)`, side `1/4` — fills the gap between A and B. -/
noncomputable def cubeD : Cube := ⟨1/4, 0, 0, 1/4, by norm_num⟩

@[simp] lemma cubeD_size : cubeD.size = 1/4 := rfl

lemma cubeD_inUnitCube : cubeD.inUnitCube := by
  unfold Cube.inUnitCube cubeD
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- A ≠ D: they differ in x-coordinate (0 vs 1/4). -/
lemma cubeA_ne_cubeD : cubeA ≠ cubeD := by
  intro h
  have hx : cubeA.x = cubeD.x := congr_arg Cube.x h
  simp only [cubeA, cubeD] at hx
  norm_num at hx

/-- B ≠ D: they differ in x-coordinate (1/2 vs 1/4). -/
lemma cubeB_ne_cubeD : cubeB ≠ cubeD := by
  intro h
  have hx : cubeB.x = cubeD.x := congr_arg Cube.x h
  simp only [cubeB, cubeD] at hx
  norm_num at hx

-- Disjointness (all x-separated, with boundary touching allowed):
--   A vs D: A.x + A.side = 1/4 ≤ 1/4 = D.x
--   D vs B: D.x + D.side = 1/2 ≤ 1/2 = B.x
--   A vs B: reuse cubeA_cubeB_disjoint (A.x + 1/4 = 1/4 ≤ 1/2 = B.x)

lemma cubeA_cubeD_disjoint : cubeA.interiorDisjoint cubeD := by
  unfold Cube.interiorDisjoint cubeA cubeD; left; norm_num

lemma cubeD_cubeA_disjoint : cubeD.interiorDisjoint cubeA := by
  unfold Cube.interiorDisjoint cubeD cubeA; right; left; norm_num

lemma cubeD_cubeB_disjoint : cubeD.interiorDisjoint cubeB := by
  unfold Cube.interiorDisjoint cubeD cubeB; left; norm_num

lemma cubeB_cubeD_disjoint : cubeB.interiorDisjoint cubeD := by
  unfold Cube.interiorDisjoint cubeB cubeD; right; left; norm_num

/-- The three-cube set `{A, B, D}`, all of size `1/4`. -/
noncomputable def triCubes : Finset Cube := {cubeA, cubeB, cubeD}

/-- The three-cube dissection — `covers_unit_cube` holds trivially. -/
noncomputable def triDissection : CubeDissection where
  cubes := triCubes
  all_contained := by
    intro c hc
    simp only [triCubes, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact cubeA_inUnitCube
    · exact cubeB_inUnitCube
    · exact cubeD_inUnitCube
  pairwise_disjoint := by
    intro c₁ hc₁ c₂ hc₂ hne
    simp only [triCubes, Finset.mem_insert, Finset.mem_singleton] at hc₁ hc₂
    rcases hc₁ with rfl | rfl | rfl <;> rcases hc₂ with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact cubeA_cubeB_disjoint
    · exact cubeA_cubeD_disjoint
    · exact cubeB_cubeA_disjoint
    · exact absurd rfl hne
    · exact cubeB_cubeD_disjoint
    · exact cubeD_cubeA_disjoint
    · exact cubeD_cubeB_disjoint
    · exact absurd rfl hne
  covers_unit_cube := trivial

lemma cubeA_mem_tri : cubeA ∈ triDissection.cubes := by
  simp [triDissection, triCubes]

lemma cubeB_mem_tri : cubeB ∈ triDissection.cubes := by
  simp [triDissection, triCubes, Finset.mem_insert, Finset.mem_singleton, cubeA_ne_cubeB.symm]

lemma cubeD_mem_tri : cubeD ∈ triDissection.cubes := by
  simp [triDissection, triCubes, Finset.mem_insert, Finset.mem_singleton,
        cubeA_ne_cubeD.symm, cubeB_ne_cubeD.symm]

/-- Membership in `collidingCubes triDissection` via the filter definition. -/
lemma mem_collidingCubes_tri_iff (c : Cube) :
    c ∈ collidingCubes triDissection ↔
      c ∈ triDissection.cubes ∧
        ∃ c' ∈ triDissection.cubes, c ≠ c' ∧ c.size = c'.size := by
  simp [collidingCubes, Finset.mem_filter]

/-- All three cubes collide (every cube has an equal-size partner). -/
lemma cubeA_collides_tri : cubeA ∈ collidingCubes triDissection := by
  rw [mem_collidingCubes_tri_iff]
  exact ⟨cubeA_mem_tri, cubeB, cubeB_mem_tri, cubeA_ne_cubeB, cubeAB_same_size⟩

lemma cubeB_collides_tri : cubeB ∈ collidingCubes triDissection := by
  rw [mem_collidingCubes_tri_iff]
  exact ⟨cubeB_mem_tri, cubeA, cubeA_mem_tri, cubeA_ne_cubeB.symm, cubeAB_same_size.symm⟩

lemma cubeD_collides_tri : cubeD ∈ collidingCubes triDissection := by
  rw [mem_collidingCubes_tri_iff]
  refine ⟨cubeD_mem_tri, cubeA, cubeA_mem_tri, cubeA_ne_cubeD.symm, ?_⟩
  simp [cubeD_size, cubeA_size]

/-- The colliding cubes of the three-cube dissection are exactly `{A, B, D}`. -/
theorem colliding_eq_tri : collidingCubes triDissection = {cubeA, cubeB, cubeD} := by
  apply Finset.Subset.antisymm
  · intro c hc
    have hmem : c ∈ triDissection.cubes := (mem_collidingCubes_tri_iff c).mp hc |>.1
    simpa only [triDissection, triCubes] using hmem
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact cubeA_collides_tri
    · exact cubeB_collides_tri
    · exact cubeD_collides_tri

/-- The three-cube dissection has exactly `3` colliding cubes. -/
theorem tri_has_three_collisions : (collidingCubes triDissection).card = 3 := by
  rw [colliding_eq_tri]
  rw [Finset.card_insert_of_not_mem, Finset.card_pair cubeB_ne_cubeD]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  push_neg
  exact ⟨cubeA_ne_cubeB, cubeA_ne_cubeD⟩

/-- `3` is attainable: the spectrum contains a value strictly above the minimum. -/
theorem three_mem_collisionSpectrum : 3 ∈ collisionSpectrum :=
  ⟨triDissection, ⟨cubeA, cubeA_mem_tri⟩, tri_has_three_collisions⟩

/-- The spectrum is a genuine nontrivial set with minimum `2`: it contains both
    `2` and `3`, and `2` is its least element. -/
theorem collisionSpectrum_nontrivial :
    {2, 3} ⊆ collisionSpectrum ∧ IsLeast collisionSpectrum 2 := by
  refine ⟨?_, isLeast_collisionSpectrum⟩
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact two_mem_collisionSpectrum
  · exact three_mem_collisionSpectrum

end DissectionOfCubesOQ01OQ02
