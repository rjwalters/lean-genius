/-
# Erdős Problem #634 (OQ-03) — The central piece meets each corner piece in a shared EDGE

Source: Erdős Problem #634 (erdosproblems.com/634), open question
`erdos-634-medial-congruence-oq-03`. Companion to
`Erdos634MedialDisjointOQ02` (interior-disjointness of the three *corner*
pieces) and `Erdos634MedialCoveringOQ02` (the covering half of the dissection).

## The gap this closes

`Erdos634MedialDisjointOQ02` proved that any two of the three *corner* medial
triangles meet in exactly a single point — the midpoint of their shared side —
and explicitly recorded the remaining case as future work:

  "Interior-disjointness against the *central* piece (a shared edge) and the area
   accounting remain for later work."

This file closes the *central-versus-corner* case. With `mAB, mBC, mCA` the three
side midpoints and

  * `pieceA   = tri A   mAB mCA`   (corner at `A`)
  * `pieceB   = tri mAB B   mBC`   (corner at `B`)
  * `pieceC   = tri mCA mBC C  `   (corner at `C`)
  * `central  = tri mBC mCA mAB`   (medial / central)

we prove, over a **non-degenerate** triangle
(`LinearIndependent ℝ ![B - A, C - A]`):

  * `pieceA_inter_central : pieceA ∩ central = segment ℝ mAB mCA`
  * `pieceB_inter_central : pieceB ∩ central = segment ℝ mAB mBC`
  * `pieceC_inter_central : pieceC ∩ central = segment ℝ mCA mBC`

i.e. the central piece overlaps each corner piece in exactly the closed segment
between the two midpoints they share — a genuine one-dimensional edge, not a
two-dimensional region. Since a segment is Lebesgue-null in the plane, this is
precisely the interior-disjointness of the central piece against each corner
piece. Combined with `Erdos634MedialDisjointOQ02`, all six pairwise overlaps of
the four medial pieces are now accounted for (three corner–corner meetings in a
point, three corner–central meetings in an edge), so the medial subdivision is a
genuine interior-disjoint tiling.

## How it is proved

The covering (`⊇`) inclusion is elementary: a point `s • mAB + t • mCA` of the
shared segment sits in the corner piece with barycentric coordinates `(0, s, t)`
and in the central piece with coordinates `(0, t, s)`, so it lies in both.

The overlap (`⊆`) inclusion is the barycentric case analysis. A point of the
corner piece at `A` has `A`-barycentric coordinate `≥ ½`, while a point of the
central piece has every barycentric coordinate `≤ ½`. On the intersection the
`A`-coordinate is forced to exactly `½`, which pins the corner-piece apex weight
`α` (and the opposite central weight) to `0` — leaving the point on the shared
segment. Uniqueness of barycentric coordinates in a non-degenerate triangle
(`bary_unique`, reused from `Erdos634MedialDisjointOQ02`) turns the two
representations into a solvable linear system, discharged by `linarith`.

Tags: geometry, erdos, dissection, tiling, interior-disjoint, edge, barycentric
-/

import Mathlib
import Proofs.Erdos634MedialDisjointOQ02

set_option linter.unusedSectionVars false

namespace Erdos634MedialCentralEdgeOQ03

open Erdos634MedialCoveringOQ02 Erdos634MedialDisjointOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The corner piece at `A` meets the central piece in exactly the segment
`[mAB, mCA]`.** The corner triangle `(A, mAB, mCA)` and the central triangle
`(mBC, mCA, mAB)` share the side joining the midpoints of `AB` and `CA`; their
overlap is precisely that closed segment. -/
theorem pieceA_inter_central {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = segment ℝ (midpoint ℝ A B) (midpoint ℝ C A) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩ := hx1
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩ := hx2
    have e1 : x = (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C
        = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (α + β / 2 + γ / 2) + (β / 2) + (γ / 2) = 1 := by linarith
    have hsb : (β' / 2 + γ' / 2) + (α' / 2 + γ' / 2) + (α' / 2 + β' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hα0 : α = 0 := by linarith
    exact ⟨β, γ, hβ, hγ, by linarith, by rw [hxe1, hα0]; module⟩
  · rintro x ⟨s, t, hs, ht, hst, hx⟩
    exact ⟨⟨0, s, t, le_refl 0, hs, ht, by linarith, by rw [← hx]; module⟩,
           ⟨0, t, s, le_refl 0, ht, hs, by linarith, by rw [← hx]; module⟩⟩

/-- **The corner piece at `B` meets the central piece in exactly the segment
`[mAB, mBC]`.** -/
theorem pieceB_inter_central {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull (midpoint ℝ A B) B (midpoint ℝ B C) ∩
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = segment ℝ (midpoint ℝ A B) (midpoint ℝ B C) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩ := hx1
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩ := hx2
    have e1 : x = (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C
        = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (α / 2) + (α / 2 + β + γ / 2) + (γ / 2) = 1 := by linarith
    have hsb : (β' / 2 + γ' / 2) + (α' / 2 + γ' / 2) + (α' / 2 + β' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hβ0 : β = 0 := by linarith
    exact ⟨α, γ, hα, hγ, by linarith, by rw [hxe1, hβ0]; module⟩
  · rintro x ⟨s, t, hs, ht, hst, hx⟩
    exact ⟨⟨s, 0, t, hs, le_refl 0, ht, by linarith, by rw [← hx]; module⟩,
           ⟨t, 0, s, ht, le_refl 0, hs, by linarith, by rw [← hx]; module⟩⟩

/-- **The corner piece at `C` meets the central piece in exactly the segment
`[mCA, mBC]`.** -/
theorem pieceC_inter_central {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull (midpoint ℝ C A) (midpoint ℝ B C) C ∩
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = segment ℝ (midpoint ℝ C A) (midpoint ℝ B C) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩ := hx1
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩ := hx2
    have e1 : x = (α / 2) • A + (β / 2) • B + (α / 2 + β / 2 + γ) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (α / 2) • A + (β / 2) • B + (α / 2 + β / 2 + γ) • C
        = (β' / 2 + γ' / 2) • A + (α' / 2 + γ' / 2) • B + (α' / 2 + β' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (α / 2) + (β / 2) + (α / 2 + β / 2 + γ) = 1 := by linarith
    have hsb : (β' / 2 + γ' / 2) + (α' / 2 + γ' / 2) + (α' / 2 + β' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hγ0 : γ = 0 := by linarith
    exact ⟨α, β, hα, hβ, by linarith, by rw [hxe1, hγ0]; module⟩
  · rintro x ⟨s, t, hs, ht, hst, hx⟩
    exact ⟨⟨s, t, 0, hs, ht, le_refl 0, by linarith, by rw [← hx]; module⟩,
           ⟨t, s, 0, ht, hs, le_refl 0, by linarith, by rw [← hx]; module⟩⟩

end Erdos634MedialCentralEdgeOQ03
