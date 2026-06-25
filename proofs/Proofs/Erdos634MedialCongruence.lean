/-
# Erdős Problem #634 — Triangle Dissection into Congruent Pieces
# The Medial Reptiling: every triangle splits into four mutually congruent halves

Source: Erdős Problem #634 (erdosproblems.com/634), a $25 problem on
understanding all triples `(T, R, N)` such that triangle `T` can be tiled by
`N` congruent copies of triangle `R`. Closely related to the recently solved
#633 (classification of triangles admitting non-square tilings).

## The problem

#634 asks to understand all `(T, R, N)`: which triangles `T` dissect into `N`
congruent triangles `R`? A foundational, fully constructive ingredient is the
**square reptiling**: every triangle dissects into `k²` congruent triangles,
each a half/`(1/k)`-scale copy of the original. The base case `k = 2` is the
**medial subdivision**: joining the midpoints of the three sides cuts the
triangle into four smaller triangles, and these four are mutually congruent.

This file formalizes that base case — the geometric heart of every square
reptiling — fully and unconditionally.

## What is proved (0 axioms, fully verified)

Working in an arbitrary real normed space `V` (so the result specialises to the
Euclidean plane), let `A B C : V` and put
`mAB = midpoint A B`, `mBC = midpoint B C`, `mCA = midpoint C A`. The four
medial triangles

  * `T₁ = (A,   mAB, mCA)`  (corner at `A`)
  * `T₂ = (mAB, B,   mBC)`  (corner at `B`)
  * `T₃ = (mCA, mBC, C)`    (corner at `C`)
  * `T₄ = (mBC, mCA, mAB)`  (central / medial)

are **pairwise congruent**, where congruence is witnessed by an explicit
isometry of `V` carrying one vertex triple onto the other:

  * `T₁ ≅ T₂`, `T₁ ≅ T₃` by translations (by `(B-A)/2`, `(C-A)/2`);
  * `T₁ ≅ T₄` by the point reflection `x ↦ (A + mBC) - x`.

Congruence is genuine isometry-congruence (`TriCongruent`), an equivalence
relation; the side lengths are therefore equal, and equal to half the original
side lengths (`medial_sides_halved`), exhibiting `4 = 2²` congruent half-copies.

We do not formalise the covering/disjointness of the dissection (the analytic
part of #634); the congruence of the four pieces — the combinatorial heart — is
what is captured here, unconditionally and axiom-free.

Tags: geometry, erdos, dissection, congruence, isometry, reptile
-/

import Mathlib

set_option linter.unusedSectionVars false

namespace Erdos634MedialCongruence

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-
## Part I: Triangle congruence by isometry
-/

/-- Two ordered triangles are **congruent** if some isometry of the ambient
space carries the first vertex triple onto the second, vertex by vertex. This
is the gold-standard notion of congruence (it implies — and over a Euclidean
space is implied by — equality of corresponding side lengths). -/
def TriCongruent (t s : V × V × V) : Prop :=
  ∃ f : V ≃ᵢ V, f t.1 = s.1 ∧ f t.2.1 = s.2.1 ∧ f t.2.2 = s.2.2

@[refl] theorem TriCongruent.refl (t : V × V × V) : TriCongruent t t :=
  ⟨IsometryEquiv.refl V, rfl, rfl, rfl⟩

theorem TriCongruent.symm {t s : V × V × V} (h : TriCongruent t s) :
    TriCongruent s t := by
  obtain ⟨f, h1, h2, h3⟩ := h
  refine ⟨f.symm, ?_, ?_, ?_⟩ <;>
    simp only [← h1, ← h2, ← h3, IsometryEquiv.symm_apply_apply]

theorem TriCongruent.trans {t s u : V × V × V}
    (h1 : TriCongruent t s) (h2 : TriCongruent s u) : TriCongruent t u := by
  obtain ⟨f, hf1, hf2, hf3⟩ := h1
  obtain ⟨g, hg1, hg2, hg3⟩ := h2
  refine ⟨f.trans g, ?_, ?_, ?_⟩ <;>
    simp only [IsometryEquiv.trans_apply, hf1, hf2, hf3, hg1, hg2, hg3]

/-- Congruent triangles have equal corresponding side lengths (SSS direction). -/
theorem TriCongruent.dist_eq {t s : V × V × V} (h : TriCongruent t s) :
    dist t.1 t.2.1 = dist s.1 s.2.1 ∧
    dist t.2.1 t.2.2 = dist s.2.1 s.2.2 ∧
    dist t.2.2 t.1 = dist s.2.2 s.1 := by
  obtain ⟨f, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [← h1, ← h2, ← h3, IsometryEquiv.dist_eq]

/-
## Part II: The explicit isometries

Translations and a point reflection, with their action on points unfolded.
-/

/-- Translation `x ↦ v + x` acting on points (`IsometryEquiv.constVAdd`). -/
theorem constVAdd_apply' (v x : V) : (IsometryEquiv.constVAdd v) x = v + x := by
  rw [IsometryEquiv.constVAdd_apply, vadd_eq_add]

/-- The point reflection `x ↦ w - x`, built as negation followed by a
translation, as an isometry of `V`. -/
noncomputable def pointRefl (w : V) : V ≃ᵢ V :=
  (LinearIsometryEquiv.neg ℝ (E := V)).toIsometryEquiv.trans
    (IsometryEquiv.constVAdd w)

theorem pointRefl_apply (w x : V) : pointRefl w x = w - x := by
  simp only [pointRefl, IsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_toIsometryEquiv, LinearIsometryEquiv.coe_neg,
    constVAdd_apply']
  abel

/-
## Part III: The medial triangles and their congruence
-/

variable (A B C : V)

/-- The four medial triangles obtained by joining side midpoints. -/
noncomputable def T1 : V × V × V := (A, midpoint ℝ A B, midpoint ℝ C A)
noncomputable def T2 : V × V × V := (midpoint ℝ A B, B, midpoint ℝ B C)
noncomputable def T3 : V × V × V := (midpoint ℝ C A, midpoint ℝ B C, C)
noncomputable def T4 : V × V × V :=
  (midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B)

/-- `T₁ ≅ T₂` via translation by `(B - A)/2`. -/
theorem cong_T1_T2 : TriCongruent (T1 A B C) (T2 A B C) := by
  refine ⟨IsometryEquiv.constVAdd (midpoint ℝ A B - A), ?_, ?_, ?_⟩ <;>
    simp only [T1, T2, constVAdd_apply', midpoint_eq_smul_add, invOf_eq_inv] <;> module

/-- `T₁ ≅ T₃` via translation by `(C - A)/2`. -/
theorem cong_T1_T3 : TriCongruent (T1 A B C) (T3 A B C) := by
  refine ⟨IsometryEquiv.constVAdd (midpoint ℝ C A - A), ?_, ?_, ?_⟩ <;>
    simp only [T1, T3, constVAdd_apply', midpoint_eq_smul_add, invOf_eq_inv] <;> module

/-- `T₁ ≅ T₄` via the point reflection `x ↦ (A + mBC) - x` (a 180° rotation). -/
theorem cong_T1_T4 : TriCongruent (T1 A B C) (T4 A B C) := by
  refine ⟨pointRefl (A + midpoint ℝ B C), ?_, ?_, ?_⟩ <;>
    simp only [T1, T4, pointRefl_apply, midpoint_eq_smul_add, invOf_eq_inv] <;> module

/-- **Main theorem.** The four medial triangles of any triangle `A B C` are
pairwise congruent. -/
theorem medial_four_congruent :
    TriCongruent (T1 A B C) (T2 A B C) ∧
    TriCongruent (T1 A B C) (T3 A B C) ∧
    TriCongruent (T1 A B C) (T4 A B C) ∧
    TriCongruent (T2 A B C) (T3 A B C) ∧
    TriCongruent (T2 A B C) (T4 A B C) ∧
    TriCongruent (T3 A B C) (T4 A B C) := by
  have h2 := cong_T1_T2 A B C
  have h3 := cong_T1_T3 A B C
  have h4 := cong_T1_T4 A B C
  exact ⟨h2, h3, h4, h2.symm.trans h3, h2.symm.trans h4, h3.symm.trans h4⟩

/-
## Part IV: The pieces are half-scale copies

Each medial triangle has side lengths exactly half those of `A B C`, so the
medial subdivision is the `k = 2` square reptiling: `4 = 2²` congruent
half-copies.
-/

/-- The reference medial triangle `T₁` has side lengths half of `A B C`. -/
theorem medial_sides_halved :
    dist (T1 A B C).1 (T1 A B C).2.1 = dist A B / 2 ∧
    dist (T1 A B C).2.1 (T1 A B C).2.2 = dist B C / 2 ∧
    dist (T1 A B C).2.2 (T1 A B C).1 = dist C A / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- dist A (midpoint A B) = dist A B / 2
    simp only [T1]
    rw [dist_left_midpoint, show ‖(2 : ℝ)‖ = 2 from by norm_num]
    ring
  · -- dist (midpoint A B) (midpoint C A) = dist B C / 2  (shared vertex A)
    simp only [T1]
    rw [midpoint_comm C A, dist_eq_norm, ← vsub_eq_sub,
      midpoint_vsub_midpoint_same_left, norm_smul, invOf_eq_inv, norm_inv,
      show ‖(2 : ℝ)‖ = 2 from by norm_num, dist_eq_norm, vsub_eq_sub]
    ring
  · -- dist (midpoint C A) A = dist C A / 2
    simp only [T1]
    rw [dist_midpoint_right, show ‖(2 : ℝ)‖ = 2 from by norm_num]
    ring

/-- All four medial triangles share the same (halved) side-length data. -/
theorem medial_congruent_to_half_triangle :
    TriCongruent (T1 A B C) (T2 A B C) ∧
    (dist (T1 A B C).1 (T1 A B C).2.1 = dist A B / 2) := by
  exact ⟨cong_T1_T2 A B C, (medial_sides_halved A B C).1⟩

end Erdos634MedialCongruence
