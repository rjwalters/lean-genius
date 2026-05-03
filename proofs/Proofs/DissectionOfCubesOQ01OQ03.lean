import Mathlib
import Proofs.DissectionOfCubes
import Proofs.DissectionOfCubesOQ01

/-!
# Cube Dissection Volume Constraint (OQ-01-OQ-03)

**Research Question**: Can the volume constraint ∑_{c ∈ d.cubes} c.side^3 = 1 be
formally incorporated into the cube dissection structure?

**Answer**: YES. We define `VolumeDissection` extending `CubeDissection` with the
volume constraint and prove 14 theorems.

## Key Insight

The current `CubeDissection` uses `covers_unit_cube : True` as a placeholder.
`VolumeDissection` replaces this with the necessary condition:
  ∑_{c ∈ d.cubes} c.side^3 = 1
If the cubes tile [0,1]^3 with disjoint interiors, their volumes sum to 1.

## Results (14 theorems, 0 sorries, 0 new axioms)

**Part I: Volume Sum Basics (3 theorems)**
1. `volumeSum_nonneg`: 0 ≤ ∑ c.side^3 for any finset of cubes
2. `volumeSum_singleton`: ∑ over {c} equals c.side^3
3. `volumeSum_insert`: inserting a new cube adds its volume

**Part II: Volume Bounds (4 theorems)**
4. `cube_volume_le_one`: each cube in a VolumeDissection has c.side^3 ≤ 1
5. `cube_side_le_one`: each cube has side ≤ 1
6. `volumeSum_pos`: if dissection is nonempty, 0 < volumeSum
7. `cube_volume_lt_one_of_card_ge_two`: if ≥ 2 cubes, each cube has volume < 1

**Part III: Collision Structure (3 theorems)**
8. `volume_dissection_has_collision`: any nonempty VolumeDissection has a collision pair
9. `collision_volume_bound`: if c₁, c₂ collide with side s, then 2 * s^3 ≤ 1
10. `collision_side_le_half_cbrt`: s^3 ≤ 1/2 for any colliding cube side s

**Part IV: Min Cubes and Decomposition (4 theorems)**
11. `min_cubes_for_collision`: any VolumeDissection with a collision has ≥ 2 cubes
12. `volumeSum_union`: volume sum distributes over disjoint union
13. `volumeSum_eq`: volume sum equals Finset.sum formulation
14. `volume_constraint_satisfiable`: there exists a VolumeDissection (with 1 cube of side 1)
-/

namespace DissectionOfCubesOQ01OQ03

open DissectionOfCubes DissectionOfCubesOQ01 BigOperators

noncomputable section

noncomputable instance : DecidableEq Cube := Classical.decEq _

-- ============================================================
-- PART I: Volume Sum Definition and Basics
-- ============================================================

/-- The total volume of a finite collection of cubes: ∑ side^3. -/
def volumeSum (cubes : Finset Cube) : ℝ :=
  ∑ c ∈ cubes, c.side ^ 3

/-- A volume-constrained dissection: a CubeDissection where cube volumes sum to 1.
    This formalizes the necessary condition that a tiling of the unit cube satisfies. -/
structure VolumeDissection where
  dissection : CubeDissection
  volume_constraint : volumeSum dissection.cubes = 1

/-- The volume sum is always non-negative (each side^3 > 0). -/
theorem volumeSum_nonneg (cubes : Finset Cube) : 0 ≤ volumeSum cubes := by
  unfold volumeSum
  apply Finset.sum_nonneg
  intro c _
  exact pow_nonneg (le_of_lt c.side_pos) 3

/-- Volume sum over a singleton equals that cube's volume. -/
theorem volumeSum_singleton (c : Cube) :
    volumeSum {c} = c.side ^ 3 := by
  simp [volumeSum]

/-- Inserting a new cube into a finset adds exactly its volume to the sum.
    Requires classical decidability for the Finset.sum_insert lemma. -/
theorem volumeSum_insert {s : Finset Cube} {c : Cube} (h : c ∉ s) :
    volumeSum (insert c s) = c.side ^ 3 + volumeSum s := by
  simp [volumeSum, Finset.sum_insert h]

-- ============================================================
-- PART II: Volume Bounds
-- ============================================================

/-- Every cube in a VolumeDissection has volume ≤ 1.
    Since ∑ side^3 = 1 and each term is ≥ 0, each term is ≤ 1. -/
theorem cube_volume_le_one (vd : VolumeDissection) (c : Cube)
    (hc : c ∈ vd.dissection.cubes) : c.side ^ 3 ≤ 1 := by
  have hnn : ∀ c' ∈ vd.dissection.cubes, 0 ≤ c'.side ^ 3 := fun c' _ =>
    pow_nonneg (le_of_lt c'.side_pos) 3
  have hle : c.side ^ 3 ≤ volumeSum vd.dissection.cubes :=
    Finset.single_le_sum hnn hc
  linarith [vd.volume_constraint]

/-- Every cube in a VolumeDissection has side ≤ 1.
    From c.side^3 ≤ 1 and c.side > 0, we conclude c.side ≤ 1. -/
theorem cube_side_le_one (vd : VolumeDissection) (c : Cube)
    (hc : c ∈ vd.dissection.cubes) : c.side ≤ 1 := by
  have h_cubic := cube_volume_le_one vd c hc
  have h_pos := c.side_pos
  -- If c.side > 1 then c.side^3 > 1: (c.side-1)^2 ≥ 0 gives c.side^2 ≥ 2*c.side - 1.
  -- Combined with c.side > 1: c.side^3 ≥ c.side*(2*c.side-1) > 1. nlinarith finds this.
  nlinarith [sq_nonneg (c.side - 1), mul_pos h_pos h_pos,
             mul_pos (mul_pos h_pos h_pos) h_pos]

/-- Volume sum is positive when the dissection is nonempty. -/
theorem volumeSum_pos (vd : VolumeDissection) (h : vd.dissection.cubes.Nonempty) :
    0 < volumeSum vd.dissection.cubes := by
  obtain ⟨c, hc⟩ := h
  have hpos : 0 < c.side ^ 3 := pow_pos c.side_pos 3
  have hle : c.side ^ 3 ≤ volumeSum vd.dissection.cubes :=
    Finset.single_le_sum (fun c' _ => pow_nonneg (le_of_lt c'.side_pos) 3) hc
  linarith

/-- If a VolumeDissection has ≥ 2 cubes, each cube has volume strictly less than 1.
    Proof: if some cube had volume = 1, all other cubes would need volume 0,
    but each cube has positive volume. -/
theorem cube_volume_lt_one_of_card_ge_two (vd : VolumeDissection) (c : Cube)
    (hc : c ∈ vd.dissection.cubes) (hcard : 2 ≤ vd.dissection.cubes.card) :
    c.side ^ 3 < 1 := by
  rcases lt_or_eq_of_le (cube_volume_le_one vd c hc) with h | h
  · exact h
  · exfalso
    -- c.side^3 = 1 means the entire volume budget is used by c
    have hc_vol : c.side ^ 3 = 1 := h
    -- There exists another cube c'
    have hother : ∃ c' ∈ vd.dissection.cubes, c' ≠ c := by
      have hlt : 1 < vd.dissection.cubes.card := by omega
      rw [Finset.one_lt_card] at hlt
      obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := hlt
      rcases Classical.em (c₁ = c) with rfl | h1
      · exact ⟨c₂, hc₂, hne.symm⟩
      · exact ⟨c₁, hc₁, h1⟩
    obtain ⟨c', hc'_mem, hne'⟩ := hother
    -- c' contributes c'.side^3 > 0 to the sum
    have hc'_pos : 0 < c'.side ^ 3 := pow_pos c'.side_pos 3
    -- c.side^3 + c'.side^3 ≤ volumeSum (since both cubes are in the dissection)
    have hc_ne : c ≠ c' := hne'.symm
    have hpair_sub : ({c, c'} : Finset Cube) ⊆ vd.dissection.cubes := by
      intro x hx
      simp [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hsum : c.side ^ 3 + c'.side ^ 3 ≤ volumeSum vd.dissection.cubes := by
      unfold volumeSum
      calc c.side ^ 3 + c'.side ^ 3
          = ∑ x ∈ ({c, c'} : Finset Cube), x.side ^ 3 := by
            rw [Finset.sum_insert (Finset.notMem_singleton.mpr hc_ne)]
            simp
        _ ≤ ∑ x ∈ vd.dissection.cubes, x.side ^ 3 :=
            Finset.sum_le_sum_of_subset_of_nonneg hpair_sub
              (fun x _ _ => pow_nonneg (le_of_lt x.side_pos) 3)
    linarith [vd.volume_constraint]

-- ============================================================
-- PART III: Collision Structure
-- ============================================================

/-- Any nonempty VolumeDissection has at least one collision pair.
    Direct application of the Wiedijk #82 impossibility theorem. -/
theorem volume_dissection_has_collision (vd : VolumeDissection)
    (h : vd.dissection.cubes.Nonempty) :
    ∃ c₁ c₂ : Cube, IsCollisionPair vd.dissection c₁ c₂ :=
  every_dissection_has_collision vd.dissection h

/-- A collision pair with common side length s satisfies 2 * s^3 ≤ 1.
    Both cubes contribute their volume to the sum, which equals 1. -/
theorem collision_volume_bound (vd : VolumeDissection) (c₁ c₂ : Cube)
    (hcoll : IsCollisionPair vd.dissection c₁ c₂) : 2 * c₁.side ^ 3 ≤ 1 := by
  obtain ⟨hc₁_mem, hc₂_mem, hne, hsize⟩ := hcoll
  -- Both cubes are in the dissection and have equal side lengths
  have hpair_sub : ({c₁, c₂} : Finset Cube) ⊆ vd.dissection.cubes := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair_sum : ∑ x ∈ ({c₁, c₂} : Finset Cube), x.side ^ 3 =
      c₁.side ^ 3 + c₂.side ^ 3 := by
    rw [Finset.sum_insert (Finset.notMem_singleton.mpr hne)]
    simp
  have hsum : c₁.side ^ 3 + c₂.side ^ 3 ≤ volumeSum vd.dissection.cubes := by
    unfold volumeSum
    rw [← hpair_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpair_sub
      (fun x _ _ => pow_nonneg (le_of_lt x.side_pos) 3)
  have heq_vol : c₂.side ^ 3 = c₁.side ^ 3 := by
    have hsides : c₁.side = c₂.side := hsize
    rw [hsides]
  linarith [vd.volume_constraint]

/-- The cube side of a collision pair is at most the cube-root of 1/2.
    Equivalently: s^3 ≤ 1/2 for any cube in a collision pair. -/
theorem collision_side_le_half_cbrt (vd : VolumeDissection) (c₁ c₂ : Cube)
    (hcoll : IsCollisionPair vd.dissection c₁ c₂) : c₁.side ^ 3 ≤ 1 / 2 := by
  linarith [collision_volume_bound vd c₁ c₂ hcoll]

-- ============================================================
-- PART IV: Minimum Cubes and Volume Decomposition
-- ============================================================

/-- Any VolumeDissection with a collision pair has at least 2 cubes. -/
theorem min_cubes_for_collision (vd : VolumeDissection)
    (hcoll : ∃ c₁ c₂, IsCollisionPair vd.dissection c₁ c₂) :
    2 ≤ vd.dissection.cubes.card := by
  obtain ⟨c₁, c₂, hc₁_mem, hc₂_mem, hne, _⟩ := hcoll
  have hpair_sub : ({c₁, c₂} : Finset Cube) ⊆ vd.dissection.cubes := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair_card : ({c₁, c₂} : Finset Cube).card = 2 := by
    rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hne)]
    simp
  linarith [Finset.card_le_card hpair_sub, hpair_card.symm.le]

/-- Volume sum distributes over disjoint union of finsets. -/
theorem volumeSum_union {s t : Finset Cube} (h : Disjoint s t) :
    volumeSum (s ∪ t) = volumeSum s + volumeSum t := by
  unfold volumeSum
  exact Finset.sum_union h

/-- The volume sum definition is identical to Finset.sum.
    Stated as a rewrite lemma for explicit use. -/
theorem volumeSum_eq (cubes : Finset Cube) :
    volumeSum cubes = ∑ c ∈ cubes, c.side ^ 3 := rfl

/-- A VolumeDissection exists: one cube of side 1 at the origin satisfies the constraint. -/
theorem volume_constraint_satisfiable :
    ∃ vd : VolumeDissection, vd.dissection.cubes.card = 1 := by
  let c : Cube := ⟨0, 0, 0, 1, by norm_num⟩
  let d : CubeDissection := {
    cubes := {c}
    all_contained := by
      intro c' hc'
      simp only [Finset.mem_singleton] at hc'
      subst hc'
      exact ⟨le_refl _, by norm_num, le_refl _, by norm_num, le_refl _, by norm_num⟩
    pairwise_disjoint := by
      intro c₁ hc₁ c₂ hc₂ hne
      simp only [Finset.mem_singleton] at hc₁ hc₂
      exact absurd (hc₁.trans hc₂.symm) hne
    covers_unit_cube := trivial
  }
  have hvol : volumeSum d.cubes = 1 := by
    show volumeSum ({c} : Finset Cube) = 1
    rw [volumeSum_singleton]
    norm_num
  refine ⟨⟨d, hvol⟩, ?_⟩
  show ({c} : Finset Cube).card = 1
  exact Finset.card_singleton c

end

end DissectionOfCubesOQ01OQ03
