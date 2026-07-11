/-
# Erdős Problem #634 (OQ-02) — The four open medial pieces are pairwise disjoint

Source: Erdős Problem #634 (erdosproblems.com/634), open question
`erdos-634-medial-congruence-oq-02`. Capstone companion to
`Erdos634MedialCoveringOQ02` (the *covering* half of the dissection),
`Erdos634MedialDisjointOQ02` (the three corner–corner overlaps are single
midpoints), and `Erdos634MedialCentralEdgeOQ03` (the three corner–central
overlaps are shared edges).

## The gap this closes

The two overlap files describe every pairwise intersection of the four *closed*
medial pieces as a shared face (a vertex or an edge). What they leave implicit is
the clean statement that makes "interior-disjoint tiling" a theorem rather than a
description: the **relative interiors** of the four pieces — the points with all
three barycentric coordinates strictly positive — are pairwise disjoint. That is
exactly the interior-disjointness condition of a genuine tiling, stated without
any appeal to Lebesgue measure or ambient dimension.

Writing `mAB, mBC, mCA` for the three side midpoints and

  * `pieceA  = tri A   mAB mCA`   (corner at `A`)
  * `pieceB  = tri mAB B   mBC`   (corner at `B`)
  * `pieceC  = tri mCA mBC C  `   (corner at `C`)
  * `central = tri mBC mCA mAB`   (medial / central)

we prove, over a **non-degenerate** triangle
(`LinearIndependent ℝ ![B - A, C - A]`), that the open piece
`triHullOpen p₁ p₂ p₃` (strict positivity `0 < a, b, c`) satisfies all six

  `triHullOpen X ∩ triHullOpen Y = ∅`

for `X ≠ Y` among the four pieces, packaged as
`medial_interiors_pairwise_disjoint`. Combined with the covering
(`Erdos634MedialCoveringOQ02.medial_covering`) this is the full tiling statement,
recorded as `medial_is_interior_disjoint_covering`.

## How it is proved

Each open corner piece has one `A B C`-barycentric coordinate strictly above
`1/2`: a point of the open corner piece at `A` has `A`-coordinate
`α + β/2 + γ/2 = (1 + α)/2 > 1/2` when `α > 0` (and symmetrically for `B`, `C`).
The open central piece has *every* `A B C`-coordinate strictly below `1/2`, since
each equals `(1 - opposite)/2`. Two of these conditions can never hold at the same
point: two corners would need two coordinates above `1/2` (their sum exceeds `1`),
and a corner versus the central piece would need one coordinate simultaneously
above and below `1/2`. Barycentric uniqueness in a non-degenerate triangle
(`bary_unique`, reused from `Erdos634MedialDisjointOQ02`) equates the two
representations, and `linarith` extracts the contradiction.

Tags: geometry, erdos, dissection, tiling, interior-disjoint, barycentric
-/

import Mathlib
import Proofs.Erdos634MedialCentralEdgeOQ03

set_option linter.unusedSectionVars false

namespace Erdos634MedialInteriorDisjointOQ02

open Erdos634MedialCoveringOQ02 Erdos634MedialDisjointOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The **relative interior** of the solid triangle on an ordered vertex triple:
all barycentric combinations `a•p₁ + b•p₂ + c•p₃` with `a, b, c` *strictly*
positive and `a + b + c = 1`. For a non-degenerate triangle this is precisely the
topological interior relative to the triangle's affine span; interior-disjointness
of the tiling is the pairwise disjointness of these sets. -/
def triHullOpen (p₁ p₂ p₃ : V) : Set V :=
  {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 1 ∧ x = a • p₁ + b • p₂ + c • p₃}

/-- The open piece is contained in the closed piece. -/
theorem triHullOpen_subset (p₁ p₂ p₃ : V) : triHullOpen p₁ p₂ p₃ ⊆ triHull p₁ p₂ p₃ := by
  rintro x ⟨a, b, c, ha, hb, hc, hs, hx⟩
  exact ⟨a, b, c, ha.le, hb.le, hc.le, hs, hx⟩

/-
## The six pairwise disjointness statements
-/

/-- The open corner pieces at `A` and `B` are disjoint. -/
theorem intA_inter_intB {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩, ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩⟩
  have e1 : x = (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C := by
    rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have e2 : x = (α' / 2) • A + (α' / 2 + β' + γ' / 2) • B + (γ' / 2) • C := by
    rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have heq : (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C
      = (α' / 2) • A + (α' / 2 + β' + γ' / 2) • B + (γ' / 2) • C := by rw [← e1, ← e2]
  have hsa : (α + β / 2 + γ / 2) + (β / 2) + (γ / 2) = 1 := by linarith
  have hsb : (α' / 2) + (α' / 2 + β' + γ' / 2) + (γ' / 2) = 1 := by linarith
  obtain ⟨E1, _, _⟩ := bary_unique hli hsa hsb heq
  linarith

/-- The open corner pieces at `B` and `C` are disjoint. -/
theorem intB_inter_intC {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) ∩
      triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩, ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩⟩
  have e1 : x = (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C := by
    rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have e2 : x = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by
    rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have heq : (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C
      = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by rw [← e1, ← e2]
  have hsa : (α / 2) + (α / 2 + β + γ / 2) + (γ / 2) = 1 := by linarith
  have hsb : (α' / 2) + (β' / 2) + (α' / 2 + β' / 2 + γ') = 1 := by linarith
  obtain ⟨_, E2, _⟩ := bary_unique hli hsa hsb heq
  linarith

/-- The open corner pieces at `A` and `C` are disjoint. -/
theorem intA_inter_intC {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩, ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩⟩
  have e1 : x = (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C := by
    rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have e2 : x = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by
    rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have heq : (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C
      = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by rw [← e1, ← e2]
  have hsa : (α + β / 2 + γ / 2) + (β / 2) + (γ / 2) = 1 := by linarith
  have hsb : (α' / 2) + (β' / 2) + (α' / 2 + β' / 2 + γ') = 1 := by linarith
  obtain ⟨E1, _, _⟩ := bary_unique hli hsa hsb heq
  linarith

/-- The open corner piece at `A` and the open central piece are disjoint. -/
theorem intA_inter_intCentral {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩, ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩⟩
  have e1 : x = (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C := by
    rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have e2 : x = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
    rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have heq : (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C
      = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
    rw [← e1, ← e2]
  have hsa : (α + β / 2 + γ / 2) + (β / 2) + (γ / 2) = 1 := by linarith
  have hsb : (β' / 2 + γ' / 2) + (α' / 2 + γ' / 2) + (α' / 2 + β' / 2) = 1 := by linarith
  obtain ⟨E1, _, _⟩ := bary_unique hli hsa hsb heq
  linarith

/-- The open corner piece at `B` and the open central piece are disjoint. -/
theorem intB_inter_intCentral {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) ∩
      triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩, ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩⟩
  have e1 : x = (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C := by
    rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have e2 : x = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
    rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have heq : (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C
      = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
    rw [← e1, ← e2]
  have hsa : (α / 2) + (α / 2 + β + γ / 2) + (γ / 2) = 1 := by linarith
  have hsb : (β' / 2 + γ' / 2) + (α' / 2 + γ' / 2) + (α' / 2 + β' / 2) = 1 := by linarith
  obtain ⟨_, E2, _⟩ := bary_unique hli hsa hsb heq
  linarith

/-- The open corner piece at `C` and the open central piece are disjoint. -/
theorem intC_inter_intCentral {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C ∩
      triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩, ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩⟩
  have e1 : x = (α / 2) • A + (β / 2) • B + (α / 2 + β / 2 + γ) • C := by
    rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have e2 : x = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
    rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
  have heq : (α / 2) • A + (β / 2) • B + (α / 2 + β / 2 + γ) • C
      = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
    rw [← e1, ← e2]
  have hsa : (α / 2) + (β / 2) + (α / 2 + β / 2 + γ) = 1 := by linarith
  have hsb : (β' / 2 + γ' / 2) + (α' / 2 + γ' / 2) + (α' / 2 + β' / 2) = 1 := by linarith
  obtain ⟨_, _, E3⟩ := bary_unique hli hsa hsb heq
  linarith

/-
## The packaged tiling statement
-/

/-- **Interior-disjointness of the medial subdivision.** All six pairwise
intersections of the open (relative-interior) medial pieces are empty. -/
theorem medial_interiors_pairwise_disjoint {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
        triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) = ∅ ∧
    triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) ∩
        triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C = ∅ ∧
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
        triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C = ∅ ∧
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
        triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ ∧
    triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) ∩
        triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ ∧
    triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C ∩
        triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ :=
  ⟨intA_inter_intB hli, intB_inter_intC hli, intA_inter_intC hli,
   intA_inter_intCentral hli, intB_inter_intCentral hli, intC_inter_intCentral hli⟩

/-- **The medial subdivision is a genuine interior-disjoint covering.** The four
closed medial pieces cover the triangle `A B C` (covering, unconditional), and
their relative interiors are pairwise disjoint (interior-disjointness, over a
non-degenerate triangle) — the two conditions that make the subdivision a tiling. -/
theorem medial_is_interior_disjoint_covering {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    (triHull A B C =
      triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∪
      triHull (midpoint ℝ A B) B (midpoint ℝ B C) ∪
      triHull (midpoint ℝ C A) (midpoint ℝ B C) C ∪
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)) ∧
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
        triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) = ∅ ∧
    triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) ∩
        triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C = ∅ ∧
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
        triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C = ∅ ∧
    triHullOpen A (midpoint ℝ A B) (midpoint ℝ C A) ∩
        triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ ∧
    triHullOpen (midpoint ℝ A B) B (midpoint ℝ B C) ∩
        triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ ∧
    triHullOpen (midpoint ℝ C A) (midpoint ℝ B C) C ∩
        triHullOpen (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) = ∅ :=
  ⟨medial_covering A B C, medial_interiors_pairwise_disjoint hli⟩

end Erdos634MedialInteriorDisjointOQ02
