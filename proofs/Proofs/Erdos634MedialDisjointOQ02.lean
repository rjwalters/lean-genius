/-
# Erdős Problem #634, oq-02 — Interior-Disjointness of the Medial Subdivision

Source: Erdős Problem #634 (erdosproblems.com/634). Companion to
`Erdos634MedialCoveringOQ02`, which proved the *covering* half of open question
oq-02: the four medial triangles of `A B C` — obtained by joining the side
midpoints — union to the whole triangle. This file supplies the complementary
*interior-disjointness* half for the three corner pieces.

Working over a **non-degenerate** triangle (`LinearIndependent ℝ ![B - A, C - A]`
— the two edge vectors at `A` are linearly independent, i.e. the triangle is not
flat), we prove:

* `bary_unique` — barycentric coordinates in a non-degenerate triangle are
  unique. This is the affine-independence non-degeneracy input, derived directly
  from `LinearIndependent.pair_iff`; no `AffineIndependent` API is needed.
* `pieceA_inter_pieceB`, `pieceB_inter_pieceC`, `pieceA_inter_pieceC` — any two of
  the three *corner* medial pieces meet in **exactly one point**, the midpoint of
  their shared side. Since a single point is measure-zero, the three corner
  pieces have disjoint interiors.

Together with the covering, this shows the medial subdivision is a genuine tiling
for the corner pieces: they cover their share and overlap only on a shared
vertex. Interior-disjointness against the *central* piece (a shared edge) and the
area accounting remain for later work.

We reuse the barycentric model `triHull` from `Erdos634MedialCoveringOQ02`, so all
statements below are genuinely about convex hulls of the vertex triples
(`triHull_eq_convexHull`).

Tags: geometry, erdos, dissection, tiling, interior-disjoint, barycentric
-/

import Mathlib
import Proofs.Erdos634MedialCoveringOQ02

set_option linter.unusedSectionVars false

namespace Erdos634MedialDisjointOQ02

open Erdos634MedialCoveringOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-
## Part I: Barycentric uniqueness (non-degeneracy)
-/

/-- **Barycentric uniqueness.** In a non-degenerate triangle (edge vectors
`B - A`, `C - A` linearly independent) a point has at most one representation as a
barycentric combination `a•A + b•B + c•C` with `a + b + c = 1`. This is the
standard affine-independence fact, obtained here directly from
`LinearIndependent.pair_iff` on the two edge vectors. -/
theorem bary_unique {A B C : V} (hli : LinearIndependent ℝ ![B - A, C - A])
    {a b c a' b' c' : ℝ} (hs : a + b + c = 1) (hs' : a' + b' + c' = 1)
    (h : a • A + b • B + c • C = a' • A + b' • B + c' • C) :
    a = a' ∧ b = b' ∧ c = c' := by
  have ha : a = 1 - b - c := by linarith
  have ha' : a' = 1 - b' - c' := by linarith
  subst ha ha'
  have hkey : (b - b') • (B - A) + (c - c') • (C - A) = 0 := by
    linear_combination (norm := module) h
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hli) (b - b') (c - c') hkey
  exact ⟨by linarith, by linarith, by linarith⟩

/-
## Part II: The three corner pieces meet only at midpoints

Each corner medial piece is a corner triangle of `A B C`: `pieceA` at `A`,
`pieceB` at `B`, `pieceC` at `C`. Two corner pieces share exactly the midpoint of
the side joining their apexes. The proofs express a point's two representations
in `A B C`-barycentric form, apply `bary_unique`, and solve a small linear
system (the two apex coordinates are forced to `1/2`, pinning the point to the
midpoint).
-/

/-- The corner pieces at `A` and `B` meet in exactly the midpoint of `A B`. -/
theorem pieceA_inter_pieceB {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHull (midpoint ℝ A B) B (midpoint ℝ B C)
      = {midpoint ℝ A B} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩ := hx1
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩ := hx2
    have e1 : x = (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (α' / 2) • A + (α' / 2 + β' + γ' / 2) • B + (γ' / 2) • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C
        = (α' / 2) • A + (α' / 2 + β' + γ' / 2) • B + (γ' / 2) • C := by
      rw [← e1, ← e2]
    have hsa : (α + β / 2 + γ / 2) + (β / 2) + (γ / 2) = 1 := by linarith
    have hsb : (α' / 2) + (α' / 2 + β' + γ' / 2) + (γ' / 2) = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hα0 : α = 0 := by linarith
    have hγ0 : γ = 0 := by linarith
    have hβ1 : β = 1 := by linarith
    show x = midpoint ℝ A B
    rw [hxe1, hα0, hβ1, hγ0]; simp
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩,
           ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩⟩

/-- The corner pieces at `B` and `C` meet in exactly the midpoint of `B C`. -/
theorem pieceB_inter_pieceC {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull (midpoint ℝ A B) B (midpoint ℝ B C) ∩
      triHull (midpoint ℝ C A) (midpoint ℝ B C) C
      = {midpoint ℝ B C} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩ := hx1
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩ := hx2
    have e1 : x = (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (α / 2) • A + (α / 2 + β + γ / 2) • B + (γ / 2) • C
        = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by
      rw [← e1, ← e2]
    have hsa : (α / 2) + (α / 2 + β + γ / 2) + (γ / 2) = 1 := by linarith
    have hsb : (α' / 2) + (β' / 2) + (α' / 2 + β' / 2 + γ') = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    have hγ1 : γ = 1 := by linarith
    show x = midpoint ℝ B C
    rw [hxe1, hα0, hβ0, hγ1]; simp
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩,
           ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩⟩

/-- The corner pieces at `A` and `C` meet in exactly the midpoint of `C A`. -/
theorem pieceA_inter_pieceC {A B C : V}
    (hli : LinearIndependent ℝ ![B - A, C - A]) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∩
      triHull (midpoint ℝ C A) (midpoint ℝ B C) C
      = {midpoint ℝ C A} := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨α, β, γ, hα, hβ, hγ, hsum1, hxe1⟩ := hx1
    obtain ⟨α', β', γ', hα', hβ', hγ', hsum2, hxe2⟩ := hx2
    have e1 : x = (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C := by
      rw [hxe1]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have e2 : x = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by
      rw [hxe2]; simp only [midpoint_eq_smul_add, invOf_eq_inv]; module
    have heq : (α + β / 2 + γ / 2) • A + (β / 2) • B + (γ / 2) • C
        = (α' / 2) • A + (β' / 2) • B + (α' / 2 + β' / 2 + γ') • C := by
      rw [← e1, ← e2]
    have hsa : (α + β / 2 + γ / 2) + (β / 2) + (γ / 2) = 1 := by linarith
    have hsb : (α' / 2) + (β' / 2) + (α' / 2 + β' / 2 + γ') = 1 := by linarith
    obtain ⟨E1, E2, E3⟩ := bary_unique hli hsa hsb heq
    have hα0 : α = 0 := by linarith
    have hβ0 : β = 0 := by linarith
    have hγ1 : γ = 1 := by linarith
    show x = midpoint ℝ C A
    rw [hxe1, hα0, hβ0, hγ1]; simp
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩,
           ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩⟩

end Erdos634MedialDisjointOQ02
