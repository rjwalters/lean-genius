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
  hypothesis).
* Step (d) discharged as standalone geometry-free lemma
  `bisector_factor_algebra` (pure-`ℝ` `linear_combination`; the algebraic
  factorization of Path A).
* Main theorem `angle_bisector_ratio_from_geometry` **now fully discharged**
  (previously the sole `sorry`): Step (c) bilinear expansion + common-norm
  cancellation produces `bisector_factor_algebra`'s hypothesis; Step (e)
  excludes the `‖u‖‖v‖ = ⟪u,v⟫` factor via
  `real_inner_div_norm_mul_norm_eq_one_iff` + `collinear_iff_of_mem` against
  `¬ Collinear ℝ {A,B,C}`; Step (f) reads off `dist B D · dist A C =
  dist D C · dist A B` from the surviving factor `(1-s)‖u‖ = s‖v‖`. Follows
  the paste-ready plan in `s5-statesync-audit-extension.md` §§4-7.
* Sorries: 0.
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

/-! ## Step (d): the algebraic factorization (geometry-free)

The crux algebra of Path A, isolated as a pure-`ℝ` lemma so it is independent
of the (Docker-gated) inner-product/Cauchy-Schwarz glue. After Step (c)'s
bilinear expansion the cosine-equality becomes

    b · ((1-s)·c² + s·iuv) = c · ((1-s)·iuv + s·b²)

(with `b := ‖C-ᵥA‖`, `c := ‖B-ᵥA‖`, `iuv := ⟪B-ᵥA, C-ᵥA⟫`). This lemma turns
that into the factorized form `((1-s)·c − s·b) · (b·c − iuv) = 0`, which the
main theorem combines with the non-collinearity exclusion (Step e) to force
the first factor to vanish, giving `s = c/(b+c)`.

The `linear_combination h` witness is verified by hand: expanding the goal's
left factor pair gives `(1-s)bc² − (1-s)c·iuv − sb²c + sb·iuv`, which equals
`h.lhs − h.rhs` term-for-term. (This resolves the sign the S5 bearer audit
§6 left as "verify by hand": the coefficient is `+h`, not `−h`.) -/
theorem bisector_factor_algebra {s b c iuv : ℝ}
    (h : b * ((1 - s) * c ^ 2 + s * iuv) = c * ((1 - s) * iuv + s * b ^ 2)) :
    ((1 - s) * c - s * b) * (b * c - iuv) = 0 := by
  linear_combination h

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
  -- Non-degeneracy: `D` cannot coincide with `A` (else `A ∈ seg(B,C)` ⟹ collinear).
  have hDA : D ≠ A := by
    intro h
    apply hncol
    have hD' : Sbtw ℝ B A C := h ▸ hD
    have hc : Collinear ℝ ({B, A, C} : Set P) := hD'.wbtw.collinear
    rwa [Set.insert_comm] at hc
  -- Nonzero vectors and norms.
  have hu_ne : (B -ᵥ A : V) ≠ 0 := vsub_ne_zero.mpr hAB.symm
  have hv_ne : (C -ᵥ A : V) ≠ 0 := vsub_ne_zero.mpr hAC.symm
  have hw_ne : (D -ᵥ A : V) ≠ 0 := vsub_ne_zero.mpr hDA
  have hun : ‖(B -ᵥ A : V)‖ ≠ 0 := norm_ne_zero_iff.mpr hu_ne
  have hvn : ‖(C -ᵥ A : V)‖ ≠ 0 := norm_ne_zero_iff.mpr hv_ne
  have hwn : ‖(D -ᵥ A : V)‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
  -- Step 1: barycentric parameter `s` placing `D` on segment `BC`.
  obtain ⟨s, hs, hw⟩ := bisector_param_exists hD A
  -- Cevian direction rewrites feeding the length lemmas.
  have hDB : D -ᵥ B = s • (C -ᵥ B) := by
    have e1 : (D -ᵥ B : V) = (D -ᵥ A) - (B -ᵥ A) := (vsub_sub_vsub_cancel_right D B A).symm
    have e2 : (C -ᵥ B : V) = (C -ᵥ A) - (B -ᵥ A) := (vsub_sub_vsub_cancel_right C B A).symm
    rw [e1, e2, hw]; module
  have hCD : C -ᵥ D = (1 - s) • (C -ᵥ B) := by
    have e1 : (C -ᵥ D : V) = (C -ᵥ A) - (D -ᵥ A) := (vsub_sub_vsub_cancel_right C D A).symm
    have e2 : (C -ᵥ B : V) = (C -ᵥ A) - (B -ᵥ A) := (vsub_sub_vsub_cancel_right C B A).symm
    rw [e1, e2, hw]; module
  -- Step 2: cevian segment lengths.
  have hDBdist : dist B D = s * dist B C := bisector_dist_BD hs hDB
  have hDCdist : dist D C = (1 - s) * dist B C := bisector_dist_DC hs hCD
  -- Step (b): cosine-equality form of the bisector hypothesis.
  have hcos := cos_BAD_eq_cos_DAC_inner_form hbis
  have hd1 : ‖(B -ᵥ A : V)‖ * ‖(D -ᵥ A : V)‖ ≠ 0 := mul_ne_zero hun hwn
  have hd2 : ‖(D -ᵥ A : V)‖ * ‖(C -ᵥ A : V)‖ ≠ 0 := mul_ne_zero hwn hvn
  rw [div_eq_div_iff hd1 hd2] at hcos
  -- Cancel the common `‖D -ᵥ A‖` from both sides.
  have h2 :
      (⟪B -ᵥ A, D -ᵥ A⟫_ℝ * ‖(C -ᵥ A : V)‖) * ‖(D -ᵥ A : V)‖
        = (⟪D -ᵥ A, C -ᵥ A⟫_ℝ * ‖(B -ᵥ A : V)‖) * ‖(D -ᵥ A : V)‖ := by
    linear_combination hcos
  have key : ⟪B -ᵥ A, D -ᵥ A⟫_ℝ * ‖(C -ᵥ A : V)‖
      = ⟪D -ᵥ A, C -ᵥ A⟫_ℝ * ‖(B -ᵥ A : V)‖ := mul_right_cancel₀ hwn h2
  -- Step (c): bilinear expansion of the two inner products via `D -ᵥ A = (1-s)u + s v`.
  have hiw : ⟪B -ᵥ A, D -ᵥ A⟫_ℝ
      = (1 - s) * ‖(B -ᵥ A : V)‖ ^ 2 + s * ⟪B -ᵥ A, C -ᵥ A⟫_ℝ := by
    rw [hw, inner_add_right, real_inner_smul_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
  have hwv : ⟪D -ᵥ A, C -ᵥ A⟫_ℝ
      = (1 - s) * ⟪B -ᵥ A, C -ᵥ A⟫_ℝ + s * ‖(C -ᵥ A : V)‖ ^ 2 := by
    rw [hw, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
  rw [hiw, hwv] at key
  -- Step (d): algebraic factorization.
  have hcc :
      ‖(C -ᵥ A : V)‖ * ((1 - s) * ‖(B -ᵥ A : V)‖ ^ 2 + s * ⟪B -ᵥ A, C -ᵥ A⟫_ℝ)
        = ‖(B -ᵥ A : V)‖ * ((1 - s) * ⟪B -ᵥ A, C -ᵥ A⟫_ℝ + s * ‖(C -ᵥ A : V)‖ ^ 2) := by
    linear_combination key
  have hfac := bisector_factor_algebra hcc
  -- Step (e)/(f): one factor vanishes; the second is excluded by non-collinearity.
  rcases mul_eq_zero.mp hfac with hL | hR
  · -- First factor zero ⟹ `s = c/(b+c)`, giving the ratio directly.
    rw [hDBdist, hDCdist,
        show dist A C = ‖(C -ᵥ A : V)‖ by rw [dist_comm]; exact dist_eq_norm_vsub V C A,
        show dist A B = ‖(B -ᵥ A : V)‖ by rw [dist_comm]; exact dist_eq_norm_vsub V B A]
    linear_combination (-(dist B C)) * hL
  · -- Second factor zero ⟹ `⟪u,v⟫ = ‖u‖‖v‖` ⟹ `A,B,C` collinear: contradiction.
    exfalso
    have h_eq : ⟪B -ᵥ A, C -ᵥ A⟫_ℝ = ‖(B -ᵥ A : V)‖ * ‖(C -ᵥ A : V)‖ := by
      have h0 : ⟪B -ᵥ A, C -ᵥ A⟫_ℝ = ‖(C -ᵥ A : V)‖ * ‖(B -ᵥ A : V)‖ := by linarith [hR]
      rw [h0, mul_comm]
    have h_div : ⟪B -ᵥ A, C -ᵥ A⟫_ℝ / (‖(B -ᵥ A : V)‖ * ‖(C -ᵥ A : V)‖) = 1 := by
      rw [h_eq]; exact div_self (mul_ne_zero hun hvn)
    obtain ⟨_, r, hr_pos, hrv⟩ :=
      (real_inner_div_norm_mul_norm_eq_one_iff (B -ᵥ A) (C -ᵥ A)).mp h_div
    have hcol : Collinear ℝ ({A, B, C} : Set P) := by
      rw [collinear_iff_of_mem (Set.mem_insert A ({B, C} : Set P))]
      refine ⟨B -ᵥ A, ?_⟩
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by rw [one_smul, vsub_vadd]⟩
      · exact ⟨r, by rw [← hrv, vsub_vadd]⟩
    exact hncol hcol

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
