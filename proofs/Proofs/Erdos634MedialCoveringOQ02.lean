/-
# Erdős Problem #634, oq-02 — The Medial Subdivision is a Covering

Source: Erdős Problem #634 (erdosproblems.com/634). Parent entry
`erdos-634-medial-congruence` proves that the four medial triangles of any
triangle `A B C` — obtained by joining the midpoints of the sides — are pairwise
congruent (isometry-congruent, half-scale copies). That entry deliberately left
the *analytic* half of the dissection unformalized, and posed as its second open
question (`erdos-634-medial-congruence-oq-02`):

> Add the covering and interior-disjointness conditions to upgrade the congruence
> statement to a genuine tiling, completing the dissection claim rather than only
> the congruence of pieces.

This file supplies the **covering** condition, unconditionally and axiom-free.

## What is proved

Working in an arbitrary real vector space `V` (so the result specialises to the
Euclidean plane), write `mAB = midpoint A B`, `mBC = midpoint B C`,
`mCA = midpoint C A`. Model the solid triangle on an ordered vertex triple by the
barycentric set

  `triHull p₁ p₂ p₃ = { a•p₁ + b•p₂ + c•p₃ | a,b,c ≥ 0, a+b+c = 1 }`,

and identify it with Mathlib's `convexHull` (`triHull_eq_convexHull`), so the
statements below are genuinely about the convex hulls of the vertex triples.

* `piece{1,2,3,4}_subset` — each of the four medial triangles is contained in the
  original triangle `A B C` (the pieces stay inside).
* `whole_subset_pieces` — every point of `A B C` lies in at least one medial
  triangle: a point with barycentric coordinates `(α,β,γ)` lands in the corner
  piece whose coordinate is `≥ 1/2`, and in the central piece when all three are
  `≤ 1/2`.
* `medial_covering` — the exact set equality: `A B C` is the union of its four
  medial triangles.
* `medial_covering_convexHull` — the same equality phrased directly with Mathlib's
  `convexHull`, the citable form of the covering.

Interior-disjointness and the measure/area accounting remain open (see the entry's
open questions); this file closes the covering half of oq-02.

Tags: geometry, erdos, dissection, tiling, covering, convex-hull, barycentric
-/

import Mathlib

set_option linter.unusedSectionVars false

namespace Erdos634MedialCoveringOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-
## Part I: The solid triangle as a barycentric set
-/

/-- The **solid triangle** on an ordered vertex triple `p₁ p₂ p₃`: all convex
combinations `a•p₁ + b•p₂ + c•p₃` with `a,b,c ≥ 0` and `a+b+c = 1`. This is the
barycentric parametrization of the filled triangle; `triHull_eq_convexHull`
identifies it with Mathlib's `convexHull`. -/
def triHull (p₁ p₂ p₃ : V) : Set V :=
  {x | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ x = a • p₁ + b • p₂ + c • p₃}

/-- `triHull` is exactly the convex hull of its three vertices, so every result
below is a statement about genuine convex hulls. -/
theorem triHull_eq_convexHull (p₁ p₂ p₃ : V) :
    triHull p₁ p₂ p₃ = convexHull ℝ {p₁, p₂, p₃} := by
  apply Set.Subset.antisymm
  · -- A barycentric combination is a convex combination of the three vertices.
    rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
    refine mem_convexHull_of_exists_fintype ![a, b, c] ![p₁, p₂, p₃] ?_ ?_ ?_ ?_
    · intro i; fin_cases i <;> simp_all
    · simpa [Fin.sum_univ_three] using hs
    · intro i; fin_cases i <;> simp
    · simp [Fin.sum_univ_three]
  · -- `triHull` is convex and contains the three vertices.
    apply convexHull_min
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by simp⟩
      · exact ⟨0, 1, 0, le_refl _, by norm_num, le_refl _, by norm_num, by simp⟩
      · exact ⟨0, 0, 1, le_refl _, le_refl _, by norm_num, by norm_num, by simp⟩
    · rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩ y ⟨a', b', c', ha', hb', hc', hs', rfl⟩
        u v hu hv huv
      exact ⟨u * a + v * a', u * b + v * b', u * c + v * c',
        by positivity, by positivity, by positivity,
        by linear_combination u * hs + v * hs' + huv, by module⟩

/-
## Part II: The pieces sit inside the original triangle
-/

/-- The corner piece at `A` is contained in the triangle `A B C`. -/
theorem piece1_subset (A B C : V) :
    triHull A (midpoint ℝ A B) (midpoint ℝ C A) ⊆ triHull A B C := by
  rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
  refine ⟨a + b / 2 + c / 2, b / 2, c / 2, by positivity, by positivity, by positivity,
    by linarith, ?_⟩
  simp only [midpoint_eq_smul_add, invOf_eq_inv]; module

/-- The corner piece at `B` is contained in the triangle `A B C`. -/
theorem piece2_subset (A B C : V) :
    triHull (midpoint ℝ A B) B (midpoint ℝ B C) ⊆ triHull A B C := by
  rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
  refine ⟨a / 2, a / 2 + b + c / 2, c / 2, by positivity, by positivity, by positivity,
    by linarith, ?_⟩
  simp only [midpoint_eq_smul_add, invOf_eq_inv]; module

/-- The corner piece at `C` is contained in the triangle `A B C`. -/
theorem piece3_subset (A B C : V) :
    triHull (midpoint ℝ C A) (midpoint ℝ B C) C ⊆ triHull A B C := by
  rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
  refine ⟨a / 2, b / 2, a / 2 + b / 2 + c, by positivity, by positivity, by positivity,
    by linarith, ?_⟩
  simp only [midpoint_eq_smul_add, invOf_eq_inv]; module

/-- The central (medial) piece is contained in the triangle `A B C`. -/
theorem piece4_subset (A B C : V) :
    triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) ⊆ triHull A B C := by
  rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
  refine ⟨b / 2 + c / 2, a / 2 + c / 2, a / 2 + b / 2, by positivity, by positivity,
    by positivity, by linarith, ?_⟩
  simp only [midpoint_eq_smul_add, invOf_eq_inv]; module

/-
## Part III: The four pieces cover the whole triangle
-/

/-- **Covering.** Every point of the triangle `A B C` lies in one of the four medial
triangles. A point with barycentric coordinates `(a,b,c)` falls into the corner
piece whose coordinate is `≥ 1/2`; if all three are `< 1/2` it falls into the
central piece. -/
theorem whole_subset_pieces (A B C : V) :
    triHull A B C ⊆
      triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∪
      triHull (midpoint ℝ A B) B (midpoint ℝ B C) ∪
      triHull (midpoint ℝ C A) (midpoint ℝ B C) C ∪
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) := by
  rintro x ⟨a, b, c, ha, hb, hc, hs, rfl⟩
  by_cases h1 : 1 / 2 ≤ a
  · refine Or.inl (Or.inl (Or.inl ⟨2 * a - 1, 2 * b, 2 * c, by linarith, by linarith,
      by linarith, by linarith, ?_⟩))
    simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
  · by_cases h2 : 1 / 2 ≤ b
    · refine Or.inl (Or.inl (Or.inr ⟨2 * a, 2 * b - 1, 2 * c, by linarith, by linarith,
        by linarith, by linarith, ?_⟩))
      simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
    · by_cases h3 : 1 / 2 ≤ c
      · refine Or.inl (Or.inr ⟨2 * a, 2 * b, 2 * c - 1, by linarith, by linarith,
          by linarith, by linarith, ?_⟩)
        simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
      · refine Or.inr ⟨1 - 2 * a, 1 - 2 * b, 1 - 2 * c, by linarith, by linarith,
          by linarith, by linarith, ?_⟩
        simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith

/-- **The medial subdivision is a covering.** The triangle `A B C` is exactly the
union of its four medial triangles. -/
theorem medial_covering (A B C : V) :
    triHull A B C =
      triHull A (midpoint ℝ A B) (midpoint ℝ C A) ∪
      triHull (midpoint ℝ A B) B (midpoint ℝ B C) ∪
      triHull (midpoint ℝ C A) (midpoint ℝ B C) C ∪
      triHull (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) := by
  refine Set.Subset.antisymm (whole_subset_pieces A B C) ?_
  refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
  · exact piece1_subset A B C
  · exact piece2_subset A B C
  · exact piece3_subset A B C
  · exact piece4_subset A B C

/-- **Covering, in Mathlib's `convexHull`.** The convex hull of `A B C` is the union
of the convex hulls of the four medial vertex triples — the citable form of the
covering condition of oq-02. -/
theorem medial_covering_convexHull (A B C : V) :
    convexHull ℝ ({A, B, C} : Set V) =
      convexHull ℝ {A, midpoint ℝ A B, midpoint ℝ C A} ∪
      convexHull ℝ {midpoint ℝ A B, B, midpoint ℝ B C} ∪
      convexHull ℝ {midpoint ℝ C A, midpoint ℝ B C, C} ∪
      convexHull ℝ {midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B} := by
  rw [← triHull_eq_convexHull, ← triHull_eq_convexHull, ← triHull_eq_convexHull,
    ← triHull_eq_convexHull, ← triHull_eq_convexHull]
  exact medial_covering A B C

end Erdos634MedialCoveringOQ02
