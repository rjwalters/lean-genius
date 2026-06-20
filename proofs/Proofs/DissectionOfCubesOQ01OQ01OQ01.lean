import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Proofs.DissectionOfCubesOQ01OQ01

/-
# Dissection of Cubes — OQ01, Sub-question 01, Sub-question 01

## Question

The gallery result `DissectionOfCubesOQ01OQ01.minimal_collision_achievable` shows that a
`CubeDissection` with exactly two colliding cubes (`HasMinimalCollision`) exists. But that
`CubeDissection` structure carries `covers_unit_cube : True` as a **placeholder**: the
geometric covering constraint is not formalized at all. The natural follow-up:

> Does the minimal-collision example survive once `covers_unit_cube` is replaced by a
> genuine geometric coverage predicate using explicit tile coordinates?

## Answer

**No — the published minimal-collision example does not survive.**

We replace the `True` placeholder with the genuine *volumetric* coverage condition

  `∑_{c ∈ cubes} c.side³ = 1`

(`GeoCubeDissection.volume_fills`). For axis-aligned, pairwise interior-disjoint cubes all
contained in `[0,1]³`, this is exactly the necessary condition for the cubes to fill the unit
cube up to measure zero — and, together with disjointness, it is *sufficient* for full-measure
coverage. It is a real geometric constraint, not `True`.

Under this predicate:

* `unitGeoDissection` (the single unit cube) is a genuine `GeoCubeDissection`, so the predicate
  is **satisfiable** — it is not vacuously empty. It has `0` colliding cubes.
* The OQ01OQ01 minimal-collision example `{cubeA, cubeB, cubeC}` (sizes 1/4, 1/4, 1/3) has
  total volume `2·(1/4)³ + (1/3)³ = 59/864 ≈ 0.068 ≠ 1`. Hence **no** `GeoCubeDissection`
  can have that cube set (`no_geo_with_exampleCubes`).

## What this establishes

The `covers_unit_cube : True` placeholder was masking a genuine obstruction: the achievability
proof in `DissectionOfCubesOQ01OQ01` exploits the freedom to place three tiny cubes anywhere
inside `[0,1]³`, leaving 93% of the volume uncovered. Once real coverage is demanded, that
construction is dead.

Whether *some* genuine volume-filling dissection achieves `HasMinimalCollision` (exactly two
colliding cubes) is the deep open geometric question — Littlewood's cascade argument suggests
the geometric constraints force strictly more than two collisions, but this is unproved. This
file does **not** resolve it; it only shows the existing combinatorial witness is not geometric.

## Honesty note

`volume_fills` formalizes *volumetric* (measure) coverage, the necessary-and-(with disjointness)-
measure-sufficient condition. It does not assert pointwise coverage of every boundary point.
All results below are `sorry`-free and `axiom`-free (they do not invoke the two geometric axioms
in `DissectionOfCubes.lean`).
-/

open DissectionOfCubes
open DissectionOfCubesOQ01
open DissectionOfCubesOQ01OQ01

namespace DissectionOfCubesOQ01OQ01OQ01

-- ============================================================
-- SECTION 1: A genuine (volumetric) cube dissection
-- ============================================================

/-- A cube dissection of the unit cube with a **genuine** coverage constraint.

    The combinatorial constraints (`all_contained`, `pairwise_disjoint`) are identical to
    `CubeDissection`, but the `True` placeholder is replaced by the real volumetric coverage
    identity `∑ c.side³ = 1`. For pairwise interior-disjoint cubes inside `[0,1]³` this is the
    necessary condition for filling the unit cube (and is measure-sufficient). -/
structure GeoCubeDissection where
  /-- The set of cubes in the dissection. -/
  cubes : Finset Cube
  /-- All cubes are contained in the unit cube. -/
  all_contained : ∀ c ∈ cubes, c.inUnitCube
  /-- Distinct cubes have disjoint interiors. -/
  pairwise_disjoint : ∀ c₁ ∈ cubes, ∀ c₂ ∈ cubes, c₁ ≠ c₂ → c₁.interiorDisjoint c₂
  /-- The cubes fill the unit cube volumetrically: the total volume equals 1. -/
  volume_fills : (∑ c ∈ cubes, c.size ^ 3) = 1

/-- Every `GeoCubeDissection` forgets to an ordinary `CubeDissection` (the placeholder
    `covers_unit_cube` is discharged by `trivial`). This lets us reuse `collidingCubes`
    and `HasMinimalCollision` unchanged. -/
def GeoCubeDissection.toCubeDissection (g : GeoCubeDissection) : CubeDissection where
  cubes := g.cubes
  all_contained := g.all_contained
  pairwise_disjoint := g.pairwise_disjoint
  covers_unit_cube := trivial

@[simp] lemma GeoCubeDissection.toCubeDissection_cubes (g : GeoCubeDissection) :
    g.toCubeDissection.cubes = g.cubes := rfl

-- ============================================================
-- SECTION 2: The predicate is satisfiable — the unit cube
-- ============================================================

/-- The unit cube `[0,1]³` itself, as a single tile. -/
noncomputable def unitCube : Cube := ⟨0, 0, 0, 1, by norm_num⟩

@[simp] lemma unitCube_size : unitCube.size = 1 := rfl

lemma unitCube_inUnitCube : unitCube.inUnitCube := by
  unfold Cube.inUnitCube unitCube
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The single unit cube is a genuine volume-filling dissection. -/
noncomputable def unitGeoDissection : GeoCubeDissection where
  cubes := {unitCube}
  all_contained := by
    intro c hc
    simp only [Finset.mem_singleton] at hc
    subst hc; exact unitCube_inUnitCube
  pairwise_disjoint := by
    intro c₁ h₁ c₂ h₂ hne
    simp only [Finset.mem_singleton] at h₁ h₂
    subst h₁; subst h₂; exact absurd rfl hne
  volume_fills := by
    rw [Finset.sum_singleton, unitCube_size]; norm_num

/-- The unit-cube dissection has **no** colliding cubes: it is a single tile, so there is
    no second cube to share its size. -/
theorem unitGeo_no_collision :
    collidingCubes unitGeoDissection.toCubeDissection = ∅ := by
  have hcubes : unitGeoDissection.toCubeDissection.cubes = {unitCube} := rfl
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  simp only [collidingCubes, Finset.mem_filter] at hc
  obtain ⟨hcmem, c', hc'mem, hne, _⟩ := hc
  rw [hcubes, Finset.mem_singleton] at hcmem hc'mem
  rw [hcmem, hc'mem] at hne
  exact hne rfl

/-- Consequently the genuine unit-cube dissection does **not** have minimal collision. -/
theorem unitGeo_not_minimal :
    ¬ HasMinimalCollision unitGeoDissection.toCubeDissection := by
  unfold HasMinimalCollision
  rw [unitGeo_no_collision, Finset.card_empty]
  norm_num

-- ============================================================
-- SECTION 3: The minimal-collision example fails genuine coverage
-- ============================================================

/-- The OQ01OQ01 minimal-collision example `{cubeA, cubeB, cubeC}` has total volume
    `2·(1/4)³ + (1/3)³ = 59/864 ≠ 1`. -/
theorem exampleCubes_volume_ne_one :
    (∑ c ∈ exampleCubes, c.size ^ 3) ≠ 1 := by
  have hAB : cubeA ∉ ({cubeB, cubeC} : Finset Cube) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨cubeA_ne_cubeB, cubeA_ne_cubeC⟩
  have hBC : cubeB ∉ ({cubeC} : Finset Cube) := by
    simp only [Finset.mem_singleton]
    exact cubeB_ne_cubeC
  show (∑ c ∈ ({cubeA, cubeB, cubeC} : Finset Cube), c.size ^ 3) ≠ 1
  rw [Finset.sum_insert hAB, Finset.sum_insert hBC, Finset.sum_singleton,
      cubeA_size, cubeB_size, cubeC_size]
  norm_num

/-- **Headline.** No genuine (volume-filling) dissection can be built from the minimal-collision
    cube set. The combinatorial witness of `minimal_collision_achievable` is therefore *not*
    geometric: replacing the `True` placeholder with real coverage destroys it. -/
theorem no_geo_with_exampleCubes :
    ¬ ∃ g : GeoCubeDissection, g.cubes = exampleCubes := by
  rintro ⟨g, hg⟩
  have hvol := g.volume_fills
  rw [hg] at hvol
  exact exampleCubes_volume_ne_one hvol

-- ============================================================
-- SECTION 4: The open question, restated under genuine coverage
-- ============================================================

/-!
### Status

* `unitGeoDissection`            — genuine coverage holds, `0` colliding cubes.
* `no_geo_with_exampleCubes`     — the published 2-collision witness is *not* geometric.

**Open question (unchanged):**

  `∃ g : GeoCubeDissection, g.cubes.Nonempty ∧ HasMinimalCollision g.toCubeDissection`

i.e. is there a *genuine* volume-filling dissection with exactly two colliding cubes?

The lower bound `DissectionOfCubesOQ01.at_least_two_colliding_cubes` still gives `≥ 2` for any
nonempty dissection (it transfers to `GeoCubeDissection` via `toCubeDissection`, since
`g.toCubeDissection.cubes = g.cubes`), so the only way `HasMinimalCollision` can fail for a
genuine multi-cube tiling is by exceeding two. Whether the geometry forces a strict excess —
Littlewood's cascade heuristic — remains open.

We deliberately do **not** re-export that lower bound as a theorem in this file: it depends on
the two geometric axioms of `DissectionOfCubes.lean` (`smaller_cube_above_axiom`,
`all_different_implies_long_chains_axiom`), and keeping it out keeps **every** result in this
file genuinely `axiom`-free. The transport is a one-liner
(`at_least_two_colliding_cubes g.toCubeDissection h`) for any consumer who wants it.
-/

end DissectionOfCubesOQ01OQ01OQ01
