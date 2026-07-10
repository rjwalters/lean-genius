/-
  Ceva's Theorem - Open Question 01-01:
  The TRIGONOMETRIC form of Ceva's theorem.

  The affine file (CevasTheoremOQ01.lean) proves the metric/affine form of
  Ceva's theorem: the cevians of a triangle are concurrent iff the product of
  the signed ratios in which they divide the opposite sides equals 1.

  This file provides the TRIGONOMETRIC ingredient, working directly with
  Mathlib's Euclidean geometry (`EuclideanGeometry.angle`, the law of sines,
  and betweenness). The heart of the trigonometric form of Ceva is the
  *cevian ratio law*: for a cevian from an apex `A` to a point `D` strictly
  between `B` and `C`,

      BD / DC = (AB · sin ∠BAD) / (AC · sin ∠DAC).

  This is a direct consequence of the law of sines applied to the two
  sub-triangles `ABD` and `ACD`, together with the fact that the angles
  `∠ADB` and `∠ADC` are supplementary (so have equal sines).

  Multiplying the cevian ratio law over the three cevians of a triangle,
  the side-length factors cancel in pairs (each side appears once in a
  numerator and once in a denominator), yielding the trigonometric Ceva
  product identity:

      (BD/DC)·(CE/EA)·(AF/FB)
        = (sin∠BAD · sin∠CBE · sin∠ACF) / (sin∠DAC · sin∠EBA · sin∠FCB).

  Combined with the affine Ceva theorem (product of side ratios = 1 iff
  concurrent), this is exactly the classical trigonometric form of Ceva's
  theorem.
-/

import Mathlib

open EuclideanGeometry Real

set_option linter.unusedVariables false

namespace TrigCeva

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace P] [NormedAddTorsor V P]

/-- Reindex a three-point non-collinearity statement across any permutation of
    the three points (collinearity depends only on the underlying set). -/
theorem ncol_perm {a b c : P} (h : ¬ Collinear ℝ ({a, b, c} : Set P))
    {x y z : P} (hs : ({x, y, z} : Set P) = {a, b, c}) :
    ¬ Collinear ℝ ({x, y, z} : Set P) := by
  rw [hs]; exact h

/-- If `A, B, C` are not collinear and `D` lies strictly between `B` and `C`,
    then the sub-triangle `A, B, D` is non-degenerate. -/
theorem not_collinear_cevian {A B C D : P}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set P)) (hBDC : Sbtw ℝ B D C) :
    ¬ Collinear ℝ ({A, B, D} : Set P) := by
  intro hcol
  apply hABC
  have hcolBDC : Collinear ℝ ({B, D, C} : Set P) := hBDC.wbtw.collinear
  have hBD : B ≠ D := hBDC.left_ne
  have hiff := hcolBDC.collinear_insert_iff_of_ne (p₁ := A) (Set.mem_insert B _)
      (Set.mem_insert_of_mem B (Set.mem_insert D _)) hBD
  have hbig : Collinear ℝ (insert A ({B, D, C} : Set P)) := hiff.mpr hcol
  refine hbig.subset ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

/-- **Cevian ratio law** (heart of the trigonometric form of Ceva's theorem).

    For a non-degenerate triangle `A B C` and a point `D` strictly between `B`
    and `C`, the ratio in which the cevian foot `D` divides `BC` is governed by
    the sines of the two angles the cevian `AD` makes at the apex:

      `dist B D / dist D C = (dist A B * sin ∠BAD) / (dist A C * sin ∠DAC)`. -/
theorem cevian_dist_ratio {A B C D : P}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set P)) (hBDC : Sbtw ℝ B D C) :
    dist B D / dist D C
      = (dist A B * Real.sin (∠ B A D)) / (dist A C * Real.sin (∠ D A C)) := by
  -- The two sub-triangles are non-degenerate.
  have hABD : ¬ Collinear ℝ ({A, B, D} : Set P) := not_collinear_cevian hABC hBDC
  have hACB : ¬ Collinear ℝ ({A, C, B} : Set P) :=
    ncol_perm hABC (by ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  have hACD : ¬ Collinear ℝ ({A, C, D} : Set P) :=
    not_collinear_cevian hACB (sbtw_comm.mp hBDC)
  -- Put them in the orderings the law of sines expects.
  have hBDA : ¬ Collinear ℝ ({B, D, A} : Set P) :=
    ncol_perm hABD (by ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  have hCDA : ¬ Collinear ℝ ({C, D, A} : Set P) :=
    ncol_perm hACD (by ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  -- Law of sines in triangles ABD and ACD.
  have hBD := dist_eq_dist_mul_sin_angle_div_sin_angle hBDA
  -- hBD : dist B D = dist A B * sin (∠ D A B) / sin (∠ B D A)
  have hCD := dist_eq_dist_mul_sin_angle_div_sin_angle hCDA
  -- hCD : dist C D = dist A C * sin (∠ D A C) / sin (∠ C D A)
  -- The angles at D are supplementary, hence have equal sines.
  have hpi : ∠ B D C = π := hBDC.angle₁₂₃_eq_pi
  have hsum : ∠ A D B + ∠ A D C = π := angle_add_angle_eq_pi_of_angle_eq_pi A hpi
  have hsin : Real.sin (∠ A D B) = Real.sin (∠ A D C) := by
    have : ∠ A D B = π - ∠ A D C := by linarith
    rw [this, Real.sin_pi_sub]
  -- The common denominator (sin of the angle at `D`) is positive.
  have hADC_pos : 0 < Real.sin (∠ A D C) :=
    sin_pos_of_not_collinear
      (ncol_perm hCDA (by ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto))
  -- Assemble.
  rw [hBD, show dist D C = dist C D from dist_comm D C, hCD,
      angle_comm B D A, angle_comm C D A, hsin, angle_comm D A B,
      div_div_div_cancel_right₀ hADC_pos.ne']

/-- **Trigonometric form of Ceva's theorem — product identity.**

    For a non-degenerate triangle `A B C` with cevian feet `D` (strictly
    between `B` and `C`), `E` (strictly between `C` and `A`) and `F` (strictly
    between `A` and `B`), the product of the three side-division ratios equals
    the product of the three sine ratios; the side-length factors cancel.

      `(BD/DC)·(CE/EA)·(AF/FB)`
        `= (sin∠BAD·sin∠CBE·sin∠ACF) / (sin∠DAC·sin∠EBA·sin∠FCB)`. -/
theorem trig_ceva_product {A B C D E F : P}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set P))
    (hD : Sbtw ℝ B D C) (hE : Sbtw ℝ C E A) (hF : Sbtw ℝ A F B) :
    (dist B D / dist D C) * (dist C E / dist E A) * (dist A F / dist F B)
      = (Real.sin (∠ B A D) * Real.sin (∠ C B E) * Real.sin (∠ A C F))
        / (Real.sin (∠ D A C) * Real.sin (∠ E B A) * Real.sin (∠ F C B)) := by
  -- Non-collinearity for the three apexes (permutations of `hABC`).
  have hBCA : ¬ Collinear ℝ ({B, C, A} : Set P) :=
    ncol_perm hABC (by ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  have hCAB : ¬ Collinear ℝ ({C, A, B} : Set P) :=
    ncol_perm hABC (by ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
  -- The three cevian ratio laws.
  have h1 := cevian_dist_ratio hABC hD
  -- h1 : dist B D / dist D C = (dist A B * sin ∠BAD) / (dist A C * sin ∠DAC)
  have h2 := cevian_dist_ratio hBCA hE
  -- h2 : dist C E / dist E A = (dist B C * sin ∠CBE) / (dist B A * sin ∠EBA)
  have h3 := cevian_dist_ratio hCAB hF
  -- h3 : dist A F / dist F B = (dist C A * sin ∠ACF) / (dist C B * sin ∠FCB)
  -- Pairwise-distinctness of the vertices (so the side lengths are nonzero).
  have hAB : A ≠ B := by
    rintro rfl
    exact hABC (by
      have hset : ({A, A, C} : Set P) = {A, C} := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]; exact collinear_pair ℝ A C)
  have hAC : A ≠ C := by
    rintro rfl
    exact hABC (by
      have hset : ({A, B, A} : Set P) = {A, B} := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]; exact collinear_pair ℝ A B)
  have hBC : B ≠ C := by
    rintro rfl
    exact hABC (by
      have hset : ({A, B, B} : Set P) = {A, B} := by
        ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]; exact collinear_pair ℝ A B)
  have hABd : dist A B ≠ 0 := dist_ne_zero.mpr hAB
  have hACd : dist A C ≠ 0 := dist_ne_zero.mpr hAC
  have hBCd : dist B C ≠ 0 := dist_ne_zero.mpr hBC
  rw [h1, h2, h3, dist_comm B A, dist_comm C A, dist_comm C B]
  field_simp

end TrigCeva
