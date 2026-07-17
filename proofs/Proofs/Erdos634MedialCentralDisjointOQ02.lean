/-
# Erdős Problem #634, oq-02 — Corner/Central Interior-Disjointness of the Medial Subdivision

Source: Erdős Problem #634 (erdosproblems.com/634). This file closes the last
qualitative gap of the medial-subdivision tiling of oq-02. `Erdos634MedialCoveringOQ02`
proved the *covering* half; `Erdos634MedialDisjointOQ02` proved that the three
**corner** pieces meet pairwise only at a shared vertex (a single point). The one
remaining overlap to pin down is each **corner** piece against the **central**
(medial) piece: unlike two corner pieces, a corner piece and the central piece
share a full *edge* — the segment joining two side-midpoints.

Working over a **non-degenerate** triangle (`LinearIndependent ℝ ![B - A, C - A]`),
we prove the three exact set equalities:

* `pieceA_inter_central` — the corner piece at `A` meets the central piece exactly
  in `segment ℝ (midpoint A B) (midpoint C A)`.
* `pieceB_inter_central` — the corner piece at `B` meets the central piece exactly
  in `segment ℝ (midpoint A B) (midpoint B C)`.
* `pieceC_inter_central` — the corner piece at `C` meets the central piece exactly
  in `segment ℝ (midpoint C A) (midpoint B C)`.

Each overlap is a one-dimensional segment (empty interior, measure zero in the
plane), so together with the pairwise corner results of `Erdos634MedialDisjointOQ02`
this establishes that the four medial pieces are **interior-disjoint**: all
overlaps lie on the shared edges/vertices of the subdivision. Combined with the
covering, the medial subdivision is a genuine (non-abstract) tiling of `A B C`,
closing the qualitative content of oq-02.

The proofs follow the `bary_unique` recipe of `Erdos634MedialDisjointOQ02`: express
a point of the intersection in `A B C`-barycentric coordinates two ways, apply
uniqueness, and solve the resulting linear system. The system forces the corner
piece's apex coordinate (and the central piece's opposite coordinate) to `0`,
pinning the point to the shared edge.

Tags: geometry, erdos, dissection, tiling, interior-disjoint, segment, barycentric
-/

import Mathlib
import Proofs.Erdos634MedialDisjointOQ02

set_option linter.unusedSectionVars false

namespace Erdos634MedialCentralDisjointOQ02

open Erdos634MedialCoveringOQ02 Erdos634MedialDisjointOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Corner piece at `A` vs. the central piece.** In a non-degenerate triangle the
corner medial piece at `A` and the central medial piece meet in exactly the shared
edge `segment ℝ (midpoint A B) (midpoint C A)`. -/
theorem pieceA_inter_central {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = segment ℝ (midpoint ℝ A B) (midpoint ℝ C A) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨a, b, c, ha, hb, hc, hsum1, hxe1⟩ := hx1
    obtain ⟨a', b', c', ha', hb', hc', hsum2, hxe2⟩ := hx2
    have e1 : x = (a + b / 2 + c / 2) • A + (b / 2) • B + (c / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (b' / 2 + c' / 2) • A + (a' / 2 + c' / 2) • B + (a' / 2 + b' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (a + b / 2 + c / 2) • A + (b / 2) • B + (c / 2) • C
        = (b' / 2 + c' / 2) • A + (a' / 2 + c' / 2) • B + (a' / 2 + b' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (a + b / 2 + c / 2) + (b / 2) + (c / 2) = 1 := by linarith
    have hsb : (b' / 2 + c' / 2) + (a' / 2 + c' / 2) + (a' / 2 + b' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have ha0 : a = 0 := by linarith
    refine ⟨b, c, hb, hc, by linarith, ?_⟩
    rw [hxe1, ha0]; simp
  · intro x hx
    obtain ⟨s, t, hs, ht, hst, hxe⟩ := hx
    refine ⟨⟨0, s, t, le_refl 0, hs, ht, by linarith, ?_⟩,
           ⟨0, t, s, le_refl 0, ht, hs, by linarith, ?_⟩⟩
    · rw [← hxe]; module
    · rw [← hxe]; module

/-- **Corner piece at `B` vs. the central piece.** The corner medial piece at `B`
and the central medial piece meet in exactly the shared edge
`segment ℝ (midpoint A B) (midpoint B C)`. -/
theorem pieceB_inter_central {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull (midpoint ℝ A B) B (midpoint ℝ B C) ∩
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = segment ℝ (midpoint ℝ A B) (midpoint ℝ B C) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨a, b, c, ha, hb, hc, hsum1, hxe1⟩ := hx1
    obtain ⟨a', b', c', ha', hb', hc', hsum2, hxe2⟩ := hx2
    have e1 : x = (a / 2) • A + (a / 2 + b + c / 2) • B + (c / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (b' / 2 + c' / 2) • A + (a' / 2 + c' / 2) • B + (a' / 2 + b' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (a / 2) • A + (a / 2 + b + c / 2) • B + (c / 2) • C
        = (b' / 2 + c' / 2) • A + (a' / 2 + c' / 2) • B + (a' / 2 + b' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (a / 2) + (a / 2 + b + c / 2) + (c / 2) = 1 := by linarith
    have hsb : (b' / 2 + c' / 2) + (a' / 2 + c' / 2) + (a' / 2 + b' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hb0 : b = 0 := by linarith
    refine ⟨a, c, ha, hc, by linarith, ?_⟩
    rw [hxe1, hb0]; simp
  · intro x hx
    obtain ⟨s, t, hs, ht, hst, hxe⟩ := hx
    refine ⟨⟨s, 0, t, hs, le_refl 0, ht, by linarith, ?_⟩,
           ⟨t, 0, s, ht, le_refl 0, hs, by linarith, ?_⟩⟩
    · rw [← hxe]; module
    · rw [← hxe]; module

/-- **Corner piece at `C` vs. the central piece.** The corner medial piece at `C`
and the central medial piece meet in exactly the shared edge
`segment ℝ (midpoint C A) (midpoint B C)`. -/
theorem pieceC_inter_central {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull (midpoint ℝ C A) (midpoint ℝ B C) C ∩
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)
      = segment ℝ (midpoint ℝ C A) (midpoint ℝ B C) := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨a, b, c, ha, hb, hc, hsum1, hxe1⟩ := hx1
    obtain ⟨a', b', c', ha', hb', hc', hsum2, hxe2⟩ := hx2
    have e1 : x = (a / 2) • A + (b / 2) • B + (a / 2 + b / 2 + c) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (b' / 2 + c' / 2) • A + (a' / 2 + c' / 2) • B + (a' / 2 + b' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (a / 2) • A + (b / 2) • B + (a / 2 + b / 2 + c) • C
        = (b' / 2 + c' / 2) • A + (a' / 2 + c' / 2) • B + (a' / 2 + b' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (a / 2) + (b / 2) + (a / 2 + b / 2 + c) = 1 := by linarith
    have hsb : (b' / 2 + c' / 2) + (a' / 2 + c' / 2) + (a' / 2 + b' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hc0 : c = 0 := by linarith
    refine ⟨a, b, ha, hb, by linarith, ?_⟩
    rw [hxe1, hc0]; simp
  · intro x hx
    obtain ⟨s, t, hs, ht, hst, hxe⟩ := hx
    refine ⟨⟨s, t, 0, hs, ht, le_refl 0, by linarith, ?_⟩,
           ⟨t, s, 0, ht, hs, le_refl 0, by linarith, ?_⟩⟩
    · rw [← hxe]; module
    · rw [← hxe]; module

end Erdos634MedialCentralDisjointOQ02
