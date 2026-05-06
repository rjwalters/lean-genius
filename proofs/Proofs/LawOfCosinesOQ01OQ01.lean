/-
  # Dual Spherical Law of Cosines
  # (law-of-cosines-oq-01-oq-01)

  For a spherical triangle with arc-length sides a, b, c and dihedral angles A, B, C:

    cos(C) = -cos(A)·cos(B) + sin(A)·sin(B)·cos(c)

  Dual to cos(c) = cos(a)cos(b) + sin(a)sin(b)cos(C) (proved in SphericalLawOfCosines.lean).

  ## Proof strategy

  1. Angles A, B at vertices V_A, V_B are dihedral angles (arccos of normalized inner product
     of perpendicular projections of the adjacent vertices).
  2. Inner-product decomposition (inner_decomposition in SphericalLawOfCosines) gives:
       cos(A)·sin(b)·sin(c) = cos(a) - cos(b)·cos(c)   [and similarly for B, C]
  3. Gram determinant Δ² = 1-cos²a-cos²b-cos²c+2cos(a)cos(b)cos(c) ≥ 0 (Cauchy-Schwarz).
  4. sin²(A)·sin²(b)·sin²(c) = Δ²  by linear_combination from the cosine formula.
  5. sin(A)·sin(B)·sin(a)·sin(b)·sin²(c) = Δ²  (nonneg product; squares to Δ⁴ by step 4).
  6. Dual law = polynomial identity; after clearing sin(a)·sin(b)·sin²(c):
       (γ-αβ)(1-γ²) + (α-βγ)(β-αγ) - γ·Δ² = 0  (verified by `ring`).

  Axiom count: 0
-/

import Proofs.SphericalLawOfCosines
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real SphericalLawOfCosines
set_option linter.unusedVariables false
set_option linter.unusedTactic false
open scoped RealInnerProductSpace

namespace DualSphericalLawOfCosines

-- ============================================================
-- Part I: Dihedral Angles at A and B
-- ============================================================

noncomputable def angleAtA (t : SphericalTriangle) : ℝ :=
  let pB := projectPerp t.B t.A
  let pC := projectPerp t.C t.A
  if h : ‖pB‖ = 0 ∨ ‖pC‖ = 0 then 0
  else Real.arccos ((@inner ℝ Vec3 _ pB pC) / (‖pB‖ * ‖pC‖))

noncomputable def angleAtB (t : SphericalTriangle) : ℝ :=
  let pA := projectPerp t.A t.B
  let pC := projectPerp t.C t.B
  if h : ‖pA‖ = 0 ∨ ‖pC‖ = 0 then 0
  else Real.arccos ((@inner ℝ Vec3 _ pA pC) / (‖pA‖ * ‖pC‖))

-- ============================================================
-- Part II: Inner Products of Perpendicular Projections
-- ============================================================

theorem inner_proj_A (t : SphericalTriangle) :
    @inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A) =
    Real.cos t.sideA - Real.cos t.sideB * Real.cos t.sideC := by
  have hd := inner_decomposition t.B t.C t.A t.hA
  rw [← cos_sideA, real_inner_comm t.B t.A, ← cos_sideC,
      real_inner_comm t.C t.A, ← cos_sideB] at hd
  linarith

theorem inner_proj_B (t : SphericalTriangle) :
    @inner ℝ Vec3 _ (projectPerp t.A t.B) (projectPerp t.C t.B) =
    Real.cos t.sideB - Real.cos t.sideA * Real.cos t.sideC := by
  have hd := inner_decomposition t.A t.C t.B t.hB
  rw [← cos_sideB, real_inner_comm t.A t.B, ← cos_sideC,
      real_inner_comm t.C t.B, ← cos_sideA] at hd
  linarith

theorem inner_proj_C (t : SphericalTriangle) :
    @inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C) =
    Real.cos t.sideC - Real.cos t.sideA * Real.cos t.sideB := by
  have hd := inner_decomposition t.A t.B t.C t.hC
  rw [← cos_sideC, real_inner_comm t.A t.C, ← cos_sideB,
      real_inner_comm t.B t.C, ← cos_sideA] at hd
  linarith

-- ============================================================
-- Part III: Norms of Projections
-- ============================================================

theorem norm_B_wrt_A (t : SphericalTriangle) : ‖projectPerp t.B t.A‖ = Real.sin t.sideC :=
  (norm_projectPerp_eq_sin t.B t.A t.hB t.hA).trans (congr_arg Real.sin (arcLength_comm t.B t.A))

theorem norm_C_wrt_A (t : SphericalTriangle) : ‖projectPerp t.C t.A‖ = Real.sin t.sideB :=
  (norm_projectPerp_eq_sin t.C t.A t.hC t.hA).trans (congr_arg Real.sin (arcLength_comm t.C t.A))

theorem norm_A_wrt_B (t : SphericalTriangle) : ‖projectPerp t.A t.B‖ = Real.sin t.sideC :=
  norm_projectPerp_eq_sin t.A t.B t.hA t.hB

theorem norm_C_wrt_B (t : SphericalTriangle) : ‖projectPerp t.C t.B‖ = Real.sin t.sideA :=
  (norm_projectPerp_eq_sin t.C t.B t.hC t.hB).trans (congr_arg Real.sin (arcLength_comm t.C t.B))

theorem norm_A_wrt_C (t : SphericalTriangle) : ‖projectPerp t.A t.C‖ = Real.sin t.sideB :=
  norm_projectPerp_eq_sin t.A t.C t.hA t.hC

theorem norm_B_wrt_C (t : SphericalTriangle) : ‖projectPerp t.B t.C‖ = Real.sin t.sideA :=
  (norm_projectPerp_eq_sin t.B t.C t.hB t.hC).trans (congr_arg Real.sin (arcLength_comm t.B t.C))

-- ============================================================
-- Part IV: Gram Determinant
-- ============================================================

noncomputable def gramDet (t : SphericalTriangle) : ℝ :=
  1 - Real.cos t.sideA ^ 2 - Real.cos t.sideB ^ 2 - Real.cos t.sideC ^ 2
    + 2 * Real.cos t.sideA * Real.cos t.sideB * Real.cos t.sideC

theorem gramDet_nonneg (t : SphericalTriangle) : 0 ≤ gramDet t := by
  -- gramDet = ‖prj(B,A)‖²·‖prj(C,A)‖² - ⟨prj(B,A),prj(C,A)⟩² ≥ 0 by Cauchy-Schwarz
  have hgap : gramDet t = ‖projectPerp t.B t.A‖ ^ 2 * ‖projectPerp t.C t.A‖ ^ 2 -
      (@inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A)) ^ 2 := by
    rw [gramDet, inner_proj_A, norm_B_wrt_A, norm_C_wrt_A]
    nlinarith [Real.sin_sq t.sideB, Real.sin_sq t.sideC]
  rw [hgap]
  nlinarith [abs_real_inner_le_norm (projectPerp t.B t.A) (projectPerp t.C t.A),
             sq_abs (@inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A)),
             norm_nonneg (projectPerp t.B t.A), norm_nonneg (projectPerp t.C t.A),
             sq_nonneg (‖projectPerp t.B t.A‖ * ‖projectPerp t.C t.A‖ -
               |@inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A)|)]

-- ============================================================
-- Part V: Cosine Formulas
-- ============================================================

private theorem abs_inner_div_le (u v : Vec3) :
    |@inner ℝ Vec3 _ u v / (‖u‖ * ‖v‖)| ≤ 1 := by
  by_cases h : ‖u‖ * ‖v‖ = 0
  · simp [h]
  · rw [abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact div_le_one_of_le₀ (abs_real_inner_le_norm u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem cos_A_mul (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.cos (angleAtA t) * Real.sin t.sideB * Real.sin t.sideC =
    Real.cos t.sideA - Real.cos t.sideB * Real.cos t.sideC := by
  have hBne : ‖projectPerp t.B t.A‖ ≠ 0 := by rw [norm_B_wrt_A]; exact ne_of_gt hc
  have hCne : ‖projectPerp t.C t.A‖ ≠ 0 := by rw [norm_C_wrt_A]; exact ne_of_gt hb
  simp only [angleAtA, dif_neg (not_or.mpr ⟨hBne, hCne⟩)]
  rw [Real.cos_arccos (abs_inner_div_le _ _), inner_proj_A, norm_B_wrt_A, norm_C_wrt_A]
  field_simp

theorem cos_B_mul (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hc : 0 < Real.sin t.sideC) :
    Real.cos (angleAtB t) * Real.sin t.sideA * Real.sin t.sideC =
    Real.cos t.sideB - Real.cos t.sideA * Real.cos t.sideC := by
  have hAne : ‖projectPerp t.A t.B‖ ≠ 0 := by rw [norm_A_wrt_B]; exact ne_of_gt hc
  have hCne : ‖projectPerp t.C t.B‖ ≠ 0 := by rw [norm_C_wrt_B]; exact ne_of_gt ha
  simp only [angleAtB, dif_neg (not_or.mpr ⟨hAne, hCne⟩)]
  rw [Real.cos_arccos (abs_inner_div_le _ _), inner_proj_B, norm_A_wrt_B, norm_C_wrt_B]
  field_simp

theorem cos_C_mul (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) :
    Real.cos t.angleC * Real.sin t.sideA * Real.sin t.sideB =
    Real.cos t.sideC - Real.cos t.sideA * Real.cos t.sideB := by
  have hAne : ‖projectPerp t.A t.C‖ ≠ 0 := by rw [norm_A_wrt_C]; exact ne_of_gt hb
  have hBne : ‖projectPerp t.B t.C‖ ≠ 0 := by rw [norm_B_wrt_C]; exact ne_of_gt ha
  simp only [SphericalTriangle.angleC, dif_neg (not_or.mpr ⟨hAne, hBne⟩)]
  rw [Real.cos_arccos (abs_inner_div_le _ _), inner_proj_C, norm_A_wrt_C, norm_B_wrt_C]
  field_simp

-- ============================================================
-- Part VI: Sine Formulas
-- ============================================================

theorem sinA_sq_gramDet (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.sin (angleAtA t) ^ 2 * Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2 = gramDet t := by
  -- Step 1: sin²A · sin²b · sin²c = sin²b·sin²c - (cos(A)·sin(b)·sin(c))²
  have h_step1 : Real.sin (angleAtA t) ^ 2 * Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2 =
      Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2 -
      (Real.cos (angleAtA t) * Real.sin t.sideB * Real.sin t.sideC) ^ 2 := by
    linear_combination (Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2) * Real.sin_sq (angleAtA t)
  -- Step 2: substitute the cosine formula cos(A)·sin(b)·sin(c) = cos(a)-cos(b)cos(c)
  rw [h_step1, cos_A_mul t hb hc]
  -- Step 3: polynomial identity sin²b·sin²c - (cos(a)-cos(b)cos(c))² = gramDet
  rw [gramDet]; nlinarith [Real.sin_sq t.sideB, Real.sin_sq t.sideC]

theorem sinB_sq_gramDet (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hc : 0 < Real.sin t.sideC) :
    Real.sin (angleAtB t) ^ 2 * Real.sin t.sideA ^ 2 * Real.sin t.sideC ^ 2 = gramDet t := by
  have h_step1 : Real.sin (angleAtB t) ^ 2 * Real.sin t.sideA ^ 2 * Real.sin t.sideC ^ 2 =
      Real.sin t.sideA ^ 2 * Real.sin t.sideC ^ 2 -
      (Real.cos (angleAtB t) * Real.sin t.sideA * Real.sin t.sideC) ^ 2 := by
    linear_combination (Real.sin t.sideA ^ 2 * Real.sin t.sideC ^ 2) * Real.sin_sq (angleAtB t)
  rw [h_step1, cos_B_mul t ha hc, gramDet]
  nlinarith [Real.sin_sq t.sideA, Real.sin_sq t.sideC]

-- ============================================================
-- Part VII: Nonnegativity of Sines of Angles
-- ============================================================

theorem sinA_nonneg (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    0 ≤ Real.sin (angleAtA t) := by
  have hBne : ‖projectPerp t.B t.A‖ ≠ 0 := by rw [norm_B_wrt_A]; exact ne_of_gt hc
  have hCne : ‖projectPerp t.C t.A‖ ≠ 0 := by rw [norm_C_wrt_A]; exact ne_of_gt hb
  simp only [angleAtA, dif_neg (not_or.mpr ⟨hBne, hCne⟩)]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

theorem sinB_nonneg (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hc : 0 < Real.sin t.sideC) :
    0 ≤ Real.sin (angleAtB t) := by
  have hAne : ‖projectPerp t.A t.B‖ ≠ 0 := by rw [norm_A_wrt_B]; exact ne_of_gt hc
  have hCne : ‖projectPerp t.C t.B‖ ≠ 0 := by rw [norm_C_wrt_B]; exact ne_of_gt ha
  simp only [angleAtB, dif_neg (not_or.mpr ⟨hAne, hCne⟩)]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

-- ============================================================
-- Part VIII: Key Product Identity
-- ============================================================

/-- sin(A)·sin(B)·sin(a)·sin(b)·sin²(c) = gramDet t.

  Both (sin(A)·sin(b)·sin(c))² and (sin(B)·sin(a)·sin(c))² equal gramDet,
  so the product squares to gramDet². Since the product is nonneg, it equals gramDet. -/
theorem sinAB_product (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.sin (angleAtA t) * Real.sin (angleAtB t) *
    Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2 = gramDet t := by
  have h_ΔA := sinA_sq_gramDet t hb hc
  have h_ΔB := sinB_sq_gramDet t ha hc
  have h_nn : 0 ≤ Real.sin (angleAtA t) * Real.sin (angleAtB t) *
      Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sinA_nonneg t hb hc) (sinB_nonneg t ha hc))
      ha.le) hb.le) (sq_nonneg _)
  have h_Δnn := gramDet_nonneg t
  -- (product)² = gramDet² by factoring and using h_ΔA, h_ΔB
  have h_sq : (Real.sin (angleAtA t) * Real.sin (angleAtB t) *
      Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2) ^ 2 = gramDet t ^ 2 := by
    have : (Real.sin (angleAtA t) * Real.sin (angleAtB t) *
        Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2) ^ 2 =
        (Real.sin (angleAtA t) ^ 2 * Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2) *
        (Real.sin (angleAtB t) ^ 2 * Real.sin t.sideA ^ 2 * Real.sin t.sideC ^ 2) := by ring
    rw [this, h_ΔA, h_ΔB]; ring
  -- (product - Δ)(product + Δ) = product² - Δ² = 0
  have h_fac : (Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.sin t.sideA *
      Real.sin t.sideB * Real.sin t.sideC ^ 2 - gramDet t) *
      (Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.sin t.sideA *
      Real.sin t.sideB * Real.sin t.sideC ^ 2 + gramDet t) = 0 := by
    have key : (Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.sin t.sideA *
        Real.sin t.sideB * Real.sin t.sideC ^ 2 - gramDet t) *
        (Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.sin t.sideA *
        Real.sin t.sideB * Real.sin t.sideC ^ 2 + gramDet t) =
        (Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.sin t.sideA *
        Real.sin t.sideB * Real.sin t.sideC ^ 2) ^ 2 - gramDet t ^ 2 := by ring
    linarith [key, h_sq]
  -- Since both factors are nonneg or both nonpos, product = Δ
  rcases mul_eq_zero.mp h_fac with h | h
  · linarith
  · linarith [h_nn, h_Δnn]

-- ============================================================
-- Part IX: Dual Spherical Law of Cosines
-- ============================================================

/-- **Dual Spherical Law of Cosines** (law-of-cosines-oq-01-oq-01)

  For a non-degenerate spherical triangle (all side sines positive):
    cos(C) = -cos(A)·cos(B) + sin(A)·sin(B)·cos(c)

  Proof: multiply both sides by sin(a)·sin(b)·sin²(c) and use the identities:
    cos(C)·sin(a)·sin(b)·sin²(c) = (cos(c)-cos(a)cos(b))·sin²(c)
    [using h_cC, h_sc2]
  and the polynomial identity (γ-αβ)(1-γ²) = (α-βγ)(β-αγ) - Δ²·γ
    [using h_cA, h_cB, h_pΔ; verified by ring].

  Axiom count: 0
-/
theorem dual_spherical_law_of_cosines (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.cos t.angleC =
      -(Real.cos (angleAtA t)) * Real.cos (angleAtB t) +
        Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.cos t.sideC := by
  have h_sc2 : Real.sin t.sideC ^ 2 = 1 - Real.cos t.sideC ^ 2 := Real.sin_sq t.sideC
  have h_cA : Real.cos (angleAtA t) * Real.sin t.sideB * Real.sin t.sideC =
      Real.cos t.sideA - Real.cos t.sideB * Real.cos t.sideC := cos_A_mul t hb hc
  have h_cB : Real.cos (angleAtB t) * Real.sin t.sideA * Real.sin t.sideC =
      Real.cos t.sideB - Real.cos t.sideA * Real.cos t.sideC := cos_B_mul t ha hc
  have h_cC : Real.cos t.angleC * Real.sin t.sideA * Real.sin t.sideB =
      Real.cos t.sideC - Real.cos t.sideA * Real.cos t.sideB := cos_C_mul t ha hb
  have h_pΔ : Real.sin (angleAtA t) * Real.sin (angleAtB t) *
      Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2 =
      1 - Real.cos t.sideA ^ 2 - Real.cos t.sideB ^ 2 - Real.cos t.sideC ^ 2 +
      2 * Real.cos t.sideA * Real.cos t.sideB * Real.cos t.sideC :=
    sinAB_product t ha hb hc
  -- The goal (cC = -cA·cB + sA·sB·γ) is equivalent to (cC - RHS) = 0.
  -- Multiply both sides by sa·sb·sc² to clear denominators.
  have h_sa_ne : Real.sin t.sideA ≠ 0 := ne_of_gt ha
  have h_sb_ne : Real.sin t.sideB ≠ 0 := ne_of_gt hb
  have h_sc_ne : Real.sin t.sideC ≠ 0 := ne_of_gt hc
  have h_dne : Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h_sa_ne h_sb_ne) (pow_ne_zero 2 h_sc_ne)
  -- Polynomial identity: expand the product and substitute the cosine/product formulas
  have h_zero : (Real.cos t.angleC - (-(Real.cos (angleAtA t) * Real.cos (angleAtB t)) +
      Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.cos t.sideC)) *
      (Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2) = 0 := by
    have expand : (Real.cos t.angleC - (-(Real.cos (angleAtA t) * Real.cos (angleAtB t)) +
        Real.sin (angleAtA t) * Real.sin (angleAtB t) * Real.cos t.sideC)) *
        (Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2) =
        (Real.cos t.angleC * Real.sin t.sideA * Real.sin t.sideB) * Real.sin t.sideC ^ 2 +
        (Real.cos (angleAtA t) * Real.sin t.sideB * Real.sin t.sideC) *
        (Real.cos (angleAtB t) * Real.sin t.sideA * Real.sin t.sideC) -
        Real.cos t.sideC * (Real.sin (angleAtA t) * Real.sin (angleAtB t) *
        Real.sin t.sideA * Real.sin t.sideB * Real.sin t.sideC ^ 2) := by ring
    rw [expand, h_cC, h_cA, h_cB, h_pΔ, h_sc2]; ring
  linarith [(mul_eq_zero.mp h_zero).resolve_right h_dne]

-- ============================================================
-- Part X: Examples
-- ============================================================

/-- At right angles (cos = 0), the dual law gives 0 = 0·0 + 1·1·0 = 0. -/
theorem dual_law_right_angles :
    Real.cos (Real.arccos (0:ℝ)) =
      -(Real.cos (Real.arccos (0:ℝ))) * Real.cos (Real.arccos (0:ℝ)) +
        Real.sin (Real.arccos (0:ℝ)) * Real.sin (Real.arccos (0:ℝ)) *
        Real.cos (Real.arccos (0:ℝ)) := by
  simp [Real.cos_arccos (by norm_num : |(0:ℝ)| ≤ 1)]

/-- Equilateral spherical triangle with angles 2π/3:
    cos(2π/3) = -(-1/2)(-1/2) + (√3/2)²·(-1/2) = -1/4 + (3/4)·(-1/2) = -1/4 - 3/8 ≠ -1/2.
    Wait — a genuine equilateral spherical triangle has EQUAL sides AND equal angles.
    For the 90-90-90 triangle (sides and angles all π/2), cos(π/2) = 0 and the law gives 0. -/
theorem dual_law_equilateral_90 :
    Real.cos (Real.arccos (0:ℝ)) = -(Real.cos (Real.arccos (0:ℝ))) * Real.cos (Real.arccos (0:ℝ)) +
        Real.sin (Real.arccos (0:ℝ)) ^ 2 * Real.cos (Real.arccos (0:ℝ)) := by
  simp [Real.cos_arccos (by norm_num : |(0:ℝ)| ≤ 1)]

end DualSphericalLawOfCosines
