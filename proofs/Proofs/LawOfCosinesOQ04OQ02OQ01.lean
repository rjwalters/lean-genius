import Mathlib
import Proofs.LawOfCosinesOQ04OQ02

/-
# Angle Bisector Ratio from Mathlib's Euclidean Geometry API

## Open Question: law-of-cosines-oq-04-oq-02-oq-01

The parent `LawOfCosinesOQ04OQ02.lean` proves the angle-bisector length formula
`t² · (b+c)² = bc · ((b+c)² − a²)` from Stewart's theorem, but takes the
**angle-bisector identity** `m · b = n · c` as an *algebraic* hypothesis (`hbis`),
rather than deriving it from the geometric premise "AD bisects ∠BAC and D ∈ seg(B,C)".

**OQ asks**: derive `m · b = n · c` directly from `Sbtw ℝ B D C` plus `∠ B A D = ∠ D A C`,
using Mathlib's `EuclideanGeometry.angle` / `dist` API, so the chained
`angle_bisector_length` becomes parametric in geometric premises only.

## Strategy (Path A — inner-product factorization)

With `u := B -ᵥ A`, `v := C -ᵥ A`:
1. From `Sbtw ℝ B D C` extract `s ∈ Ioo (0:ℝ) 1` with `D -ᵥ A = (1 - s) • u + s • v`.
2. Compute `dist B D = s · dist B C` and `dist D C = (1 - s) · dist B C`.
3. Expand cosines: `cos(∠BAD)` and `cos(∠DAC)` in terms of `s, ⟪u,v⟫, ‖u‖, ‖v‖, ‖D-ᵥA‖`.
4. From `∠BAD = ∠DAC` (and `arccos` injectivity on `[-1,1]`) derive the cosine equality
   ⇒ algebraic factorization `((1-s)·c − s·b) · (b·c − ⟪u,v⟫) = 0`.
5. The non-degeneracy hypothesis `¬ Collinear ℝ ({A,B,C} : Set P)` plus strict Cauchy-Schwarz
   rules out the second factor; conclude `s = c/(b+c)`, hence `m · b = n · c`.

## Mathlib bearers (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0)

* `Sbtw.mem_image_Ioo` — `Mathlib/Analysis/Convex/Between.lean:353`
* `AffineMap.lineMap_apply` — `lineMap a b t = a + t • (b -ᵥ a)`
* `EuclideanGeometry.angle` (def) — `Geometry/Euclidean/Angle/Unoriented/Affine.lean:42`
* `InnerProductGeometry.cos_angle` — `Geometry/Euclidean/Angle/Unoriented/Basic.lean:65`
* `Real.arccos_inj` — `Analysis/SpecialFunctions/Trigonometric/Inverse.lean:336`
* `dist_eq_norm_vsub` — `Analysis/Normed/Group/AddTorsor.lean:76`
* `abs_real_inner_le_norm` — `Analysis/InnerProductSpace/Basic.lean:453`
* `EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi`
  — `Affine.lean:378`

See `research/problems/law-of-cosines-oq-04-oq-02-oq-01/s2-prep-bearer-audit.md` for
the full audit table and re-grounded line numbers at the pinned SHA.

## Status

* S3 progress: Steps 1–2 of Path A discharged
  (`bisector_param_exists`, `bisector_dist_BD`, `bisector_dist_DC`).
* S6a progress: Step (b) discharged as helper
  `cos_BAD_eq_cos_DAC_inner_form` (cosine-equality form of the bisector
  hypothesis). Main theorem still has 1 sorry (Steps c-f remain).
* Sorries: 1 (`angle_bisector_ratio_from_geometry` — the main theorem).
* Axioms: 0.
-/

open EuclideanGeometry
open scoped InnerProductSpace

namespace LawOfCosinesOQ04OQ02OQ01

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P]

/-! ## Step 1: Barycentric parameter for D on segment BC

From `Sbtw ℝ B D C` extract `s ∈ Ioo 0 1` placing `D` on the open segment with
`D -ᵥ A = (1 - s) • (B -ᵥ A) + s • (C -ᵥ A)`. This is the unique parameter
`s = dist B D / dist B C` (deferred to `bisector_dist_BD` below).

Proof outline:
* `Sbtw.mem_image_Ioo` yields `⟨s, hs, hD⟩` with `s ∈ Ioo 0 1` and `lineMap B C s = D`.
* `AffineMap.lineMap_apply` rewrites `lineMap B C s = B + s • (C -ᵥ B)`.
* Subtracting `A` and using `vsub` lemmas converts to the affine combination
  `(1 - s) • (B -ᵥ A) + s • (C -ᵥ A)`. -/
lemma bisector_param_exists {B C D : P} (hD : Sbtw ℝ B D C) (A : P) :
    ∃ s : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 ∧
      D -ᵥ A = (1 - s) • (B -ᵥ A) + s • (C -ᵥ A) := by
  obtain ⟨s, hs, hlm⟩ := hD.mem_image_Ioo
  refine ⟨s, hs, ?_⟩
  have hDeq : D = AffineMap.lineMap B C s := hlm.symm
  have hCB : (C -ᵥ B : V) = (C -ᵥ A) - (B -ᵥ A) :=
    (vsub_sub_vsub_cancel_right C B A).symm
  rw [hDeq, AffineMap.lineMap_apply, vadd_vsub_assoc, hCB,
      smul_sub, sub_smul, one_smul]
  abel

/-! ## Step 2: Cevian segment lengths

With `s` the barycentric parameter from Step 1:
* `dist B D = s · dist B C`,
* `dist D C = (1 - s) · dist B C`.

These follow from `dist_eq_norm_vsub` + `norm_smul` once we express `D -ᵥ B` and
`C -ᵥ D` in terms of `s • (C -ᵥ B)` and `(1-s) • (C -ᵥ B)`. -/
lemma bisector_dist_BD {B C D : P} {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hD : D -ᵥ B = s • (C -ᵥ B)) :
    dist B D = s * dist B C := by
  have hs_nonneg : (0 : ℝ) ≤ s := hs.1.le
  calc dist B D
      = dist D B := dist_comm _ _
    _ = ‖D -ᵥ B‖ := dist_eq_norm_vsub V D B
    _ = ‖s • (C -ᵥ B)‖ := by rw [hD]
    _ = ‖s‖ * ‖C -ᵥ B‖ := norm_smul s (C -ᵥ B)
    _ = s * ‖C -ᵥ B‖ := by rw [Real.norm_of_nonneg hs_nonneg]
    _ = s * dist C B := by rw [dist_eq_norm_vsub V C B]
    _ = s * dist B C := by rw [dist_comm]

lemma bisector_dist_DC {B C D : P} {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hD : C -ᵥ D = (1 - s) • (C -ᵥ B)) :
    dist D C = (1 - s) * dist B C := by
  have h1s_nonneg : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  calc dist D C
      = dist C D := dist_comm _ _
    _ = ‖C -ᵥ D‖ := dist_eq_norm_vsub V C D
    _ = ‖(1 - s) • (C -ᵥ B)‖ := by rw [hD]
    _ = ‖1 - s‖ * ‖C -ᵥ B‖ := norm_smul (1 - s) (C -ᵥ B)
    _ = (1 - s) * ‖C -ᵥ B‖ := by rw [Real.norm_of_nonneg h1s_nonneg]
    _ = (1 - s) * dist C B := by rw [dist_eq_norm_vsub V C B]
    _ = (1 - s) * dist B C := by rw [dist_comm]

/-! ## Step (b): cosine-equality form of the angle-bisector hypothesis

Converts `hbis : ∠ B A D = ∠ D A C` into the inner-product cosine equation
`⟪B-ᵥA, D-ᵥA⟫ / (‖B-ᵥA‖·‖D-ᵥA‖) = ⟪D-ᵥA, C-ᵥA⟫ / (‖D-ᵥA‖·‖C-ᵥA‖)`.

Strategy: apply `Real.cos` to both sides of `hbis`, unfold
`EuclideanGeometry.angle` (definitionally `InnerProductGeometry.angle` on
vsub-vectors), then rewrite both sides with `InnerProductGeometry.cos_angle`.

The `congrArg Real.cos hbis` route avoids the `[-1, 1]` bound obligations that
the `Real.arccos_inj` alternative would require (see
`research/problems/law-of-cosines-oq-04-oq-02-oq-01/s4-prep-step-b-and-e-bearer-audit.md` § 2.3). -/
lemma cos_BAD_eq_cos_DAC_inner_form
    {A B C D : P} (hbis : ∠ B A D = ∠ D A C) :
    ⟪B -ᵥ A, D -ᵥ A⟫_ℝ / (‖B -ᵥ A‖ * ‖D -ᵥ A‖)
      = ⟪D -ᵥ A, C -ᵥ A⟫_ℝ / (‖D -ᵥ A‖ * ‖C -ᵥ A‖) := by
  have hcos : Real.cos (∠ B A D) = Real.cos (∠ D A C) := congrArg Real.cos hbis
  unfold EuclideanGeometry.angle at hcos
  rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle] at hcos
  exact hcos

/-! ## Main theorem: geometric angle-bisector identity

`m · b = n · c` derived from the bisector angle equality `∠ B A D = ∠ D A C`
and `Sbtw ℝ B D C`. The non-degeneracy hypothesis `¬ Collinear ℝ ({A,B,C} : Set P)`
is required for the strict-Cauchy-Schwarz step (Step 5 of the strategy).

Proof skeleton (Path A, S5/S6 refinement of `s5-statesync-audit-extension.md` §§ 4-7):
1. Extract `s` via `bisector_param_exists`.
2. Cosine equality via `cos_BAD_eq_cos_DAC_inner_form` (Step b, discharged above).
3. Inner-product bilinear expansion (S5 § 5: `inner_add/sub/smul_left/right`).
4. Algebraic factorization `((1-s)c − sb)(bc − ⟪u,v⟫) = 0` via `linear_combination` (S5 § 6).
5. Exclude `bc = ⟪u,v⟫` via `real_inner_div_norm_mul_norm_eq_one_iff` +
   `angle_eq_zero_iff_ne_and_wbtw` + `Wbtw.collinear` (S5 § 4).
6. Conclude `s = c/(b+c)`, hence `m·b = n·c` after multiplying through by `dist B C` (S5 § 7). -/
theorem angle_bisector_ratio_from_geometry
    {A B C D : P}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hncol : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hD : Sbtw ℝ B D C)
    (hbis : ∠ B A D = ∠ D A C) :
    dist B D * dist A C = dist D C * dist A B := by
  sorry

/-! ## Downstream chaining (deferred to S3)

Once `angle_bisector_ratio_from_geometry` is discharged, we can re-state the
parent's `angle_bisector_length` purely in geometric terms by:

* feeding `hbis := angle_bisector_ratio_from_geometry …` (rewritten as
  `dist B D * dist A C = dist D C * dist A B` matching the parent's
  `m * b = n * c` with `m = dist B D, n = dist D C, b = dist A C, c = dist A B`);
* deriving `ha : dist B D + dist D C = dist B C` from `Sbtw.dist_add_dist`
  (Mathlib `Convex/Between.lean`);
* discharging the parent's `h_ABD : c² = t² + m² - 2tmu` and
  `h_ACD : b² = t² + n² + 2tnu` from `EuclideanGeometry.dist_sq_eq_...`
  in `Geometry/Euclidean/Triangle.lean`.

The chained statement (target for S4):
```
theorem angle_bisector_length_geometric
    (A B C D : P) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hncol : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hD : Sbtw ℝ B D C) (hbis : ∠ B A D = ∠ D A C) :
    (dist A D)^2 * (dist A C + dist A B)^2 =
      (dist A C * dist A B) * ((dist A C + dist A B)^2 - (dist B C)^2)
```

This packages the entire Mathlib gap (`Geometry.Euclidean.AngleBisector` candidate
module — see `knowledge.md §6` and `§8`). -/

end LawOfCosinesOQ04OQ02OQ01
