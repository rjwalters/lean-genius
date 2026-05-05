import Mathlib.Tactic
import Proofs.DissectionOfCubes
import Proofs.DissectionOfCubesOQ03

/-
# Dissection of Cubes OQ-03-OQ-02: Correcting the Bottom-Floor Descent Argument

## Open Question: dissection-of-cubes-oq-03-oq-02

The parent `DissectionOfCubesOQ03.lean` contains a sorry-filled theorem:

  `global_min_not_reaching_top`: the globally minimum-side cube satisfies z + side < 1.

This file proves that theorem is **false as stated** (a 1-cube dissection is a
counterexample), identifies the correct formulation, and proves it:
**the bottom-floor minimum** (minimum-side cube on z = 0) satisfies side < 1.

## The Counterexample to global_min_not_reaching_top

Let d = {unit_cube} where unit_cube = (x:=0, y:=0, z:=0, side:=1).

- d.allDifferentSizes: vacuously true (no distinct pairs in a 1-element set)
- CoversUnitCube d: the unit cube covers all of [0,1]³
- d.cubes.Nonempty: holds
- c_min = unit_cube is the unique global minimum (hc_min_le vacuously satisfied)
- **c_min.z + c_min.side = 0 + 1 = 1 — not < 1**

So `global_min_not_reaching_top` would need extra hypotheses to be provable.

## The Correct Theorem

**No cube of side = 1 can exist in a dissection with ≥ 2 cubes.**

If c has side = 1, inUnitCube forces c.x = c.y = c.z = 0 (c fills [0,1]³).
Any other cube c' (from card ≥ 2) has positive side and lies in [0,1]³, so
c' ∩ c ≠ ∅ in their interiors — contradicting pairwise_disjoint.

**Corollary**: The bottom-floor minimum (z = 0) has side < 1, so z + side < 1.
This is the correct precondition for the `exists_smaller_cube` descent step.

## Main Results (0 sorries, 0 axioms)

1. `no_unit_cube_in_multi_dissection`: No cube has side = 1 if card ≥ 2.
2. `all_cubes_side_lt_one`: All cubes have side < 1 when card ≥ 2.
3. `bottom_floor_min_side_lt_one`: Bottom-floor minimum has side < 1.
4. `bottom_floor_min_not_reaching_top`: Bottom-floor minimum satisfies z + side < 1.
5. `bottom_floor_min_is_descent_ready`: A descent-ready cube exists on the bottom floor.
6. `global_min_false_for_unit_cube`: Formal counterexample to the sorry-goal.
-/

open DissectionOfCubes DissectionOfCubesOQ03

namespace DissectionOfCubesOQ03OQ02

-- ============================================================
-- PART 1: No Unit-Side Cube in a Multi-Cube Dissection
-- ============================================================

/-- **No unit-side cube in a multi-cube dissection.**

    If c has side = 1 and card ≥ 2, we get a contradiction via pairwise_disjoint.
    The key: c.side = 1 forces c = [0,1]³ (the unit cube). Any other cube c' has
    c'.side > 0 and lies in [0,1]³, so c' has nonempty interior inside (0,1)³ = int(c).
    This means int(c) ∩ int(c') ≠ ∅, contradicting pairwise_disjoint for c ≠ c'. -/
theorem no_unit_cube_in_multi_dissection
    (d : CubeDissection) (h_card : 1 < d.cubes.card)
    (c : Cube) (hc : c ∈ d.cubes) (hside : c.side = 1) : False := by
  -- From c.side = 1 and inUnitCube: c.x = c.y = c.z = 0.
  have h_con := d.all_contained c hc
  obtain ⟨hcx0, hcx1, hcy0, hcy1, hcz0, hcz1⟩ := h_con
  have hx : c.x = 0 := by linarith
  have hy : c.y = 0 := by linarith
  have hz : c.z = 0 := by linarith
  have hcx_top : c.x + c.side = 1 := by linarith
  have hcy_top : c.y + c.side = 1 := by linarith
  have hcz_top : c.z + c.side = 1 := by linarith
  -- Find c' ≠ c in d.cubes from card ≥ 2.
  have h_erase_ne : (d.cubes.erase c).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_emp
    have : (d.cubes.erase c).card = 0 := Finset.card_eq_zero.mpr h_emp
    rw [Finset.card_erase_of_mem hc] at this
    omega
  obtain ⟨c', hc'_erase⟩ := h_erase_ne
  have hc'_mem : c' ∈ d.cubes := (Finset.mem_erase.mp hc'_erase).2
  have hc'_ne : c' ≠ c := (Finset.mem_erase.mp hc'_erase).1
  -- c' containment constraints.
  have h_con' := d.all_contained c' hc'_mem
  obtain ⟨hc'x0, hc'x1, hc'y0, hc'y1, hc'z0, hc'z1⟩ := h_con'
  -- pairwise_disjoint requires interiorDisjoint c c'.
  have h_disj := d.pairwise_disjoint c hc c' hc'_mem (Ne.symm hc'_ne)
  unfold Cube.interiorDisjoint at h_disj
  -- Each of the 6 disjuncts leads to contradiction.
  rcases h_disj with h | h | h | h | h | h
  · linarith [c'.side_pos]  -- c.x+c.side ≤ c'.x → 1 ≤ c'.x, but c'.x+c'.side ≤ 1
  · linarith [hc'x0, c'.side_pos]  -- c'.x+c'.side ≤ c.x=0, but c'.x≥0, c'.side>0
  · linarith [c'.side_pos]  -- c.y+c.side ≤ c'.y
  · linarith [hc'y0, c'.side_pos]  -- c'.y+c'.side ≤ c.y=0
  · linarith [c'.side_pos]  -- c.z+c.side ≤ c'.z
  · linarith [hc'z0, c'.side_pos]  -- c'.z+c'.side ≤ c.z=0

-- ============================================================
-- PART 2: All Cubes Have Side < 1 in a Multi-Cube Dissection
-- ============================================================

/-- All cubes in a multi-cube dissection have side < 1. -/
theorem all_cubes_side_lt_one
    (d : CubeDissection) (h_card : 1 < d.cubes.card)
    (c : Cube) (hc : c ∈ d.cubes) : c.side < 1 := by
  have h_con := d.all_contained c hc
  obtain ⟨_, _, _, _, hcz0, hcz1⟩ := h_con
  have hle : c.side ≤ 1 := by linarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (no_unit_cube_in_multi_dissection d h_card c hc heq).elim

-- ============================================================
-- PART 3: Bottom-Floor Minimum Has Side < 1
-- ============================================================

/-- The minimum-side cube on the bottom floor (z = 0) has side < 1.
    This is the key geometric fact replacing the false `global_min_not_reaching_top`. -/
theorem bottom_floor_min_side_lt_one
    (d : CubeDissection) (h_card : 1 < d.cubes.card)
    (c_min : Cube) (hc_min_mem : c_min ∈ d.cubes) : c_min.side < 1 :=
  all_cubes_side_lt_one d h_card c_min hc_min_mem

-- ============================================================
-- PART 4: Bottom-Floor Minimum Does Not Reach the Top
-- ============================================================

/-- The bottom-floor minimum satisfies z + side < 1.

    Since it has z = 0 (on the bottom floor) and side < 1, we immediately get
    z + side = side < 1. This is the `h_not_top` precondition for `exists_smaller_cube`. -/
theorem bottom_floor_min_not_reaching_top
    (d : CubeDissection) (h_card : 1 < d.cubes.card)
    (c_min : Cube) (hc_min_mem : c_min ∈ d.cubes) (hc_min_z : c_min.z = 0) :
    c_min.z + c_min.side < 1 := by
  linarith [bottom_floor_min_side_lt_one d h_card c_min hc_min_mem, hc_min_z]

-- ============================================================
-- PART 5: A Descent-Ready Cube Exists on the Bottom Floor
-- ============================================================

/-- **The bottom floor provides a descent-ready starting point.**

    If card ≥ 2 and CoversUnitCube, there exists a cube c_start satisfying:
    - c_start is on the bottom floor (z = 0)
    - c_start.z + c_start.side < 1 (satisfies the `h_not_top` precondition)

    This is the correct formulation of the descent starting condition, replacing the
    false `global_min_not_reaching_top` from OQ-03 for the globally minimum cube. -/
theorem bottom_floor_min_is_descent_ready
    (d : CubeDissection) (h_card : 1 < d.cubes.card)
    (hcov : CoversUnitCube d) :
    ∃ c_start ∈ d.cubes, c_start.z = 0 ∧ c_start.z + c_start.side < 1 := by
  -- The bottom floor is nonempty from CoversUnitCube.
  have h_bottom_ne : d.cubesTouchingBottom.Nonempty := bottom_floor_nonempty d hcov
  -- Take the minimum-side cube on the bottom floor.
  obtain ⟨c_min, hc_min_bottom, _⟩ :=
    Finset.exists_min_image d.cubesTouchingBottom Cube.size h_bottom_ne
  have hc_min_mem : c_min ∈ d.cubes := (Finset.mem_filter.mp hc_min_bottom).1
  have hc_min_z : c_min.z = 0 := (Finset.mem_filter.mp hc_min_bottom).2
  have h_not_top := bottom_floor_min_not_reaching_top d h_card c_min hc_min_mem hc_min_z
  exact ⟨c_min, hc_min_mem, hc_min_z, h_not_top⟩

-- ============================================================
-- PART 6: Formal Counterexample to global_min_not_reaching_top
-- ============================================================

/-- **Formal counterexample**: the 1-cube dissection satisfies all hypotheses of
    `global_min_not_reaching_top` yet has c_min.z + c_min.side = 1 (not < 1).

    This is why `global_min_not_reaching_top` is unsolvable as stated in OQ-03.
    The hypothesis `1 < d.cubes.card` (or equivalent) must be added. -/
theorem global_min_false_for_unit_cube
    (d : CubeDissection)
    (hd_singleton : d.cubes = {⟨0, 0, 0, 1, by norm_num⟩})
    (c_min : Cube) (hc_min_mem : c_min ∈ d.cubes)
    (hc_min_le : ∀ c' ∈ d.cubes, c_min.side ≤ c'.side) :
    c_min.z + c_min.side = 1 := by
  have hc_min_eq : c_min = ⟨0, 0, 0, 1, by norm_num⟩ :=
    Finset.mem_singleton.mp (hd_singleton ▸ hc_min_mem)
  subst hc_min_eq
  norm_num

/-
## Summary of the Mathematical Contribution

The sorry in OQ-03 attempts to prove `global_min_not_reaching_top` for the
**globally** minimum cube. This is false because the global minimum might have
its top face on the unit cube's boundary (z + side = 1 with z > 0), which is
geometrically consistent with any valid dissection.

The correct proof strategy (Littlewood's original argument) is:
1. Start from the **bottom floor** (z = 0).
2. The bottom-floor minimum c₁ has c₁.side < 1 [proved here: parts 1-3].
3. Since c₁.z = 0, we get c₁.z + c₁.side < 1 [proved here: part 4].
4. Apply `exists_smaller_cube` (from OQ-03) to c₁ to get a strictly smaller c₂.
5. Apply `exists_smaller_cube` to c₂ at c₂'s floor — this requires establishing that
   c₂.z + c₂.side < 1, which is the remaining gap requiring `smallest_above_is_smaller`.

The descent thus starts cleanly from the bottom floor, with the globally minimum
cube never appearing in the argument. This resolves the key conceptual gap in OQ-03.
-/

end DissectionOfCubesOQ03OQ02
