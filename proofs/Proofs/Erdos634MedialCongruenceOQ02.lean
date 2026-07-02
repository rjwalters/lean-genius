/-
# Erdős Problem #634 (OQ-02) — The medial subdivision is a genuine COVERING

Source: open question `erdos-634-medial-congruence-oq-02`, the analytic
companion of the base entry `Proofs.Erdos634MedialCongruence`.

## The gap this closes

The base entry proves that the four medial triangles obtained by joining the
side midpoints of `A B C`,

  * `T₁ = (A,   mAB, mCA)`  (corner at `A`)
  * `T₂ = (mAB, B,   mBC)`  (corner at `B`)
  * `T₃ = (mCA, mBC, C)`    (corner at `C`)
  * `T₄ = (mBC, mCA, mAB)`  (central / medial)

are **pairwise congruent**.  It explicitly disclaims the *covering* half of the
dissection statement: "We do not formalise the covering/disjointness of the
dissection (the analytic part of #634)".

This file supplies the covering half.  Writing `tri A B C` for the filled
triangle (all convex combinations `a•A + b•B + c•C`, `a,b,c ≥ 0`, `a+b+c = 1`),
the main result is

  `medial_covering :  tri A B C = tri A mAB mCA ∪ tri mAB B mBC
                                  ∪ tri mCA mBC C ∪ tri mBC mCA mAB`

i.e. the four medial triangles together cover the whole triangle, with no point
left out.  Combined with the base entry's congruence result, this promotes the
medial subdivision from "four congruent pieces" to "four congruent pieces that
tile the triangle" (covering being the analytic ingredient the base entry left
open).

## What is proved (0 axioms, fully verified)

Working over an arbitrary real vector space `V` (`AddCommGroup V`, `Module ℝ V`)
— no norm or metric is needed, since covering is a purely affine/convex
property:

  * `triBary_convex`        : the barycentric triangle region is convex;
  * `triBary_eq_convexHull` : it is exactly the convex hull of the three
    vertices — so `tri A B C` is genuinely *the* triangle, in Mathlib's sense;
  * `medial_covering`       : the four medial sub-triangles cover `tri A B C`
    exactly (set equality), the covering half of the dissection;
  * `medial_covering_convexHull` : the same statement phrased with `convexHull`.

The covering direction is the barycentric case analysis: a point with
barycentric coordinates `(a,b,c)` lies in the corner triangle at `A` when
`a ≥ ½` (symmetrically for `B`, `C`), and in the central medial triangle when
all three coordinates are `≤ ½`; the explicit reweightings are given.

The remaining ingredient for a *measure-theoretic* tiling — interior
disjointness (the pairwise overlaps of the four pieces are the shared edges,
hence Lebesgue-null in the plane) — is not formalised here; it requires fixing
`V = ℝ²` and the planar area measure, and is recorded as future work.

Tags: geometry, erdos, dissection, tiling, covering, convexity, barycentric
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Module
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false

namespace Erdos634MedialCongruenceOQ02

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The filled triangle with vertices `A B C`, in barycentric form: all convex
combinations `a•A + b•B + c•C` with `a, b, c ≥ 0` and `a + b + c = 1`. -/
def triBary (A B C : V) : Set V :=
  {p | ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 1 ∧ p = a • A + b • B + c • C}

/-- Each vertex belongs to its own triangle. -/
theorem left_mem_triBary (A B C : V) : A ∈ triBary A B C :=
  ⟨1, 0, 0, by norm_num, le_refl 0, le_refl 0, by norm_num, by module⟩

theorem middle_mem_triBary (A B C : V) : B ∈ triBary A B C :=
  ⟨0, 1, 0, le_refl 0, by norm_num, le_refl 0, by norm_num, by module⟩

theorem right_mem_triBary (A B C : V) : C ∈ triBary A B C :=
  ⟨0, 0, 1, le_refl 0, le_refl 0, by norm_num, by norm_num, by module⟩

/-- The barycentric triangle region is convex. -/
theorem triBary_convex (A B C : V) : Convex ℝ (triBary A B C) := by
  rintro p ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, hsum₁, rfl⟩
    q ⟨a₂, b₂, c₂, ha₂, hb₂, hc₂, hsum₂, rfl⟩ s t hs ht hst
  refine ⟨s * a₁ + t * a₂, s * b₁ + t * b₂, s * c₁ + t * c₂,
    add_nonneg (mul_nonneg hs ha₁) (mul_nonneg ht ha₂),
    add_nonneg (mul_nonneg hs hb₁) (mul_nonneg ht hb₂),
    add_nonneg (mul_nonneg hs hc₁) (mul_nonneg ht hc₂), ?_, ?_⟩
  · have h : s * a₁ + t * a₂ + (s * b₁ + t * b₂) + (s * c₁ + t * c₂)
      = s * (a₁ + b₁ + c₁) + t * (a₂ + b₂ + c₂) := by ring
    rw [h, hsum₁, hsum₂]; linarith
  · module

/-- `tri A B C` is exactly the convex hull of its three vertices: the
barycentric description agrees with Mathlib's `convexHull`. -/
theorem triBary_eq_convexHull (A B C : V) :
    triBary A B C = convexHull ℝ ({A, B, C} : Set V) := by
  apply le_antisymm
  · rintro p ⟨a, b, c, ha, hb, hc, hsum, rfl⟩
    have hA : A ∈ convexHull ℝ ({A, B, C} : Set V) := subset_convexHull ℝ _ (by simp)
    have hB : B ∈ convexHull ℝ ({A, B, C} : Set V) := subset_convexHull ℝ _ (by simp)
    have hC : C ∈ convexHull ℝ ({A, B, C} : Set V) := subset_convexHull ℝ _ (by simp)
    have h0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ ![a, b, c] i := by
      intro i _; fin_cases i <;> assumption
    have h1 : ∑ i : Fin 3, ![a, b, c] i = 1 := by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      linarith
    have h2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        ![A, B, C] i ∈ convexHull ℝ ({A, B, C} : Set V) := by
      intro i _; fin_cases i
      · exact hA
      · exact hB
      · exact hC
    have hmem := (convex_convexHull ℝ ({A, B, C} : Set V)).sum_mem h0 h1 h2
    simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] using hmem
  · refine convexHull_min ?_ (triBary_convex A B C)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact left_mem_triBary _ _ _
    · exact middle_mem_triBary _ _ _
    · exact right_mem_triBary _ _ _

/-- **The medial subdivision covers the triangle.**  With `mAB, mBC, mCA` the
three side midpoints, the four medial sub-triangles

  `(A, mAB, mCA)`, `(mAB, B, mBC)`, `(mCA, mBC, C)`, `(mBC, mCA, mAB)`

cover `tri A B C` exactly — every point of the triangle lies in at least one of
them, and each of them lies inside the triangle. -/
theorem medial_covering (A B C : V) :
    triBary A B C =
      triBary A (midpoint ℝ A B) (midpoint ℝ C A) ∪
      triBary (midpoint ℝ A B) B (midpoint ℝ B C) ∪
      triBary (midpoint ℝ C A) (midpoint ℝ B C) C ∪
      triBary (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B) := by
  ext p
  constructor
  · -- Covering: every point of the triangle lands in one of the four pieces.
    rintro ⟨a, b, c, ha, hb, hc, hsum, rfl⟩
    rcases le_or_gt (1 / 2 : ℝ) a with hA | hA
    · -- corner triangle at `A`
      refine Or.inl (Or.inl (Or.inl ⟨2 * a - 1, 2 * b, 2 * c,
        by linarith, by linarith, by linarith, by linarith, ?_⟩))
      simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
    · rcases le_or_gt (1 / 2 : ℝ) b with hB | hB
      · -- corner triangle at `B`
        refine Or.inl (Or.inl (Or.inr ⟨2 * a, 2 * b - 1, 2 * c,
          by linarith, by linarith, by linarith, by linarith, ?_⟩))
        simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
      · rcases le_or_gt (1 / 2 : ℝ) c with hC | hC
        · -- corner triangle at `C`
          refine Or.inl (Or.inr ⟨2 * a, 2 * b, 2 * c - 1,
            by linarith, by linarith, by linarith, by linarith, ?_⟩)
          simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
        · -- central medial triangle
          refine Or.inr ⟨1 - 2 * a, 1 - 2 * b, 1 - 2 * c,
            by linarith, by linarith, by linarith, by linarith, ?_⟩
          simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith
  · -- Each of the four pieces sits inside the triangle.
    rintro (((⟨a, b, c, ha, hb, hc, hsum, rfl⟩ | ⟨a, b, c, ha, hb, hc, hsum, rfl⟩) |
      ⟨a, b, c, ha, hb, hc, hsum, rfl⟩) | ⟨a, b, c, ha, hb, hc, hsum, rfl⟩)
    · exact ⟨a + b / 2 + c / 2, b / 2, c / 2, by linarith, by linarith, by linarith,
        by linarith, by simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith⟩
    · exact ⟨a / 2, a / 2 + b + c / 2, c / 2, by linarith, by linarith, by linarith,
        by linarith, by simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith⟩
    · exact ⟨a / 2, b / 2, a / 2 + b / 2 + c, by linarith, by linarith, by linarith,
        by linarith, by simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith⟩
    · exact ⟨(b + c) / 2, (a + c) / 2, (a + b) / 2, by linarith, by linarith, by linarith,
        by linarith, by simp only [midpoint_eq_smul_add, invOf_eq_inv]; match_scalars <;> linarith⟩

/-- The covering statement phrased with Mathlib's `convexHull`: the convex hull
of the three vertices is the union of the convex hulls of the four medial
sub-triangles. -/
theorem medial_covering_convexHull (A B C : V) :
    convexHull ℝ ({A, B, C} : Set V) =
      convexHull ℝ ({A, midpoint ℝ A B, midpoint ℝ C A} : Set V) ∪
      convexHull ℝ ({midpoint ℝ A B, B, midpoint ℝ B C} : Set V) ∪
      convexHull ℝ ({midpoint ℝ C A, midpoint ℝ B C, C} : Set V) ∪
      convexHull ℝ ({midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B} : Set V) := by
  have h := medial_covering A B C
  simp only [triBary_eq_convexHull] at h
  exact h

end Erdos634MedialCongruenceOQ02
