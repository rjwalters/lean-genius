/-
  Spherical Law of Sines (law-of-cosines-oq-01-oq-02)

  For a spherical triangle on the unit sphere S² with arc-length sides a, b, c
  and dihedral angles A, B, C (at the opposite vertices):

    sin(a)·sin(B) = sin(b)·sin(A)   [multiplicative law of sines]

  Equivalently (when sin(A), sin(B) > 0): sin(a)/sin(A) = sin(b)/sin(B).

  ## Proof Strategy

  The Gram determinant G = 1-cos²a-cos²b-cos²c+2cos(a)cos(b)cos(c) satisfies:
    G = sin²b·sin²c - (cos(a)-cos(b)·cos(c))²    [pure ring]
    G ≥ 0                                          [Cauchy-Schwarz on projections]

  From the spherical law of cosines at vertex A:
    cos(A) = (cos(a)-cos(b)cos(c))/(sin(b)sin(c))

  Therefore sin²A·sin²b·sin²c = G (by substitution + ring).
  By symmetry: sin²B·sin²a·sin²c = G.
  Cancelling sin²c: sin²A·sin²b = sin²B·sin²a.
  Taking non-negative square roots: sin(A)·sin(b) = sin(B)·sin(a).

  ## References
  - Todhunter, "Spherical Trigonometry" (1886) §17-18
  - Builds on: SphericalLawOfCosines.lean (same gallery)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Proofs.SphericalLawOfCosines

open Real SphericalLawOfCosines

set_option maxHeartbeats 800000

-- Extend SphericalTriangle with dihedral angles at A and B.
-- Placed in SphericalLawOfCosines so dot notation t.angleA / t.angleB works.
namespace SphericalLawOfCosines

/-- The dihedral angle at vertex A of a spherical triangle. -/
noncomputable def SphericalTriangle.angleA (t : SphericalTriangle) : ℝ :=
  let pB := projectPerp t.B t.A
  let pC := projectPerp t.C t.A
  if ‖pB‖ = 0 ∨ ‖pC‖ = 0 then 0
  else Real.arccos ((@inner ℝ Vec3 _ pB pC) / (‖pB‖ * ‖pC‖))

/-- The dihedral angle at vertex B of a spherical triangle. -/
noncomputable def SphericalTriangle.angleB (t : SphericalTriangle) : ℝ :=
  let pA := projectPerp t.A t.B
  let pC := projectPerp t.C t.B
  if ‖pA‖ = 0 ∨ ‖pC‖ = 0 then 0
  else Real.arccos ((@inner ℝ Vec3 _ pA pC) / (‖pA‖ * ‖pC‖))

end SphericalLawOfCosines

namespace LawOfCosinesOQ01OQ02

-- ============================================================================
-- Part I: Inner Product of Projections
-- ============================================================================

/-- The inner product of the projections of B and C onto the plane ⊥ to A
    equals cos(a) - cos(b)·cos(c).
    Direct consequence of the inner decomposition (spherical law of cosines at A). -/
lemma proj_inner_eq (t : SphericalTriangle) :
    @inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A) =
    Real.cos t.sideA - Real.cos t.sideB * Real.cos t.sideC := by
  have h := spherical_law_of_cosines_algebraic t.B t.C t.A t.hB t.hC t.hA
  -- real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫ (Mathlib 4.26 ordering)
  rw [← cos_sideA, real_inner_comm t.A t.B, ← cos_sideC,
      real_inner_comm t.A t.C, ← cos_sideB] at h
  linarith

/-- ‖projectPerp B A‖ = sin(sideC) = sin(arcLength A B). -/
lemma norm_proj_BA (t : SphericalTriangle) :
    ‖projectPerp t.B t.A‖ = Real.sin t.sideC :=
  (norm_projectPerp_eq_sin t.B t.A t.hB t.hA).trans (congr_arg Real.sin (arcLength_comm t.B t.A))

/-- ‖projectPerp C A‖ = sin(sideB) = sin(arcLength A C). -/
lemma norm_proj_CA (t : SphericalTriangle) :
    ‖projectPerp t.C t.A‖ = Real.sin t.sideB :=
  (norm_projectPerp_eq_sin t.C t.A t.hC t.hA).trans (congr_arg Real.sin (arcLength_comm t.C t.A))

/-- ‖projectPerp A B‖ = sin(sideC) = sin(arcLength B A). -/
lemma norm_proj_AB (t : SphericalTriangle) :
    ‖projectPerp t.A t.B‖ = Real.sin t.sideC :=
  norm_projectPerp_eq_sin t.A t.B t.hA t.hB

/-- ‖projectPerp C B‖ = sin(sideA) = sin(arcLength B C). -/
lemma norm_proj_CB (t : SphericalTriangle) :
    ‖projectPerp t.C t.B‖ = Real.sin t.sideA :=
  (norm_projectPerp_eq_sin t.C t.B t.hC t.hB).trans (congr_arg Real.sin (arcLength_comm t.C t.B))

/-- Inner product of projections of A, C onto plane ⊥ to B equals cos(b)-cos(a)cos(c). -/
lemma proj_inner_eq_B (t : SphericalTriangle) :
    @inner ℝ Vec3 _ (projectPerp t.A t.B) (projectPerp t.C t.B) =
    Real.cos t.sideB - Real.cos t.sideA * Real.cos t.sideC := by
  have h := spherical_law_of_cosines_algebraic t.A t.C t.B t.hA t.hC t.hB
  rw [← cos_sideB, ← cos_sideC, real_inner_comm t.B t.C, ← cos_sideA] at h
  linarith

-- ============================================================================
-- Part II: Gram Determinant
-- ============================================================================

/-- The Gram determinant: G = 1 - cos²a - cos²b - cos²c + 2cos(a)cos(b)cos(c). -/
noncomputable def gramDet (t : SphericalTriangle) : ℝ :=
  1 - Real.cos t.sideA ^ 2 - Real.cos t.sideB ^ 2 - Real.cos t.sideC ^ 2 +
  2 * Real.cos t.sideA * Real.cos t.sideB * Real.cos t.sideC

/-- G = sin²b·sin²c - (cos(a) - cos(b)cos(c))². Pure ring computation. -/
lemma gramDet_expand (t : SphericalTriangle) :
    gramDet t = Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2 -
      (Real.cos t.sideA - Real.cos t.sideB * Real.cos t.sideC) ^ 2 := by
  simp only [gramDet, Real.sin_sq]; ring

/-- G = ‖projB_A‖²·‖projC_A‖² - ⟨projB_A, projC_A⟩². -/
lemma gramDet_as_proj (t : SphericalTriangle) :
    gramDet t = ‖projectPerp t.B t.A‖ ^ 2 * ‖projectPerp t.C t.A‖ ^ 2 -
      @inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A) ^ 2 := by
  rw [gramDet_expand, proj_inner_eq, norm_proj_BA, norm_proj_CA]
  ring

/-- The Gram determinant is non-negative (Cauchy-Schwarz inequality). -/
lemma gramDet_nonneg (t : SphericalTriangle) : 0 ≤ gramDet t := by
  rw [gramDet_as_proj]
  set x := projectPerp t.B t.A with hx_def
  set y := projectPerp t.C t.A with hy_def
  have h_cs := abs_real_inner_le_norm x y
  have h_norm_nn : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_abs_sq_le : |@inner ℝ Vec3 _ x y| ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h_cs 2
  have h_abs_sq : |@inner ℝ Vec3 _ x y| ^ 2 = @inner ℝ Vec3 _ x y ^ 2 := sq_abs _
  rw [h_abs_sq, mul_pow] at h_abs_sq_le
  linarith

-- ============================================================================
-- Part III: Dihedral Angles
-- ============================================================================

/-- sin(angleA) ≥ 0 since angleA ∈ [0, π]. -/
lemma sin_angleA_nonneg (t : SphericalTriangle) : 0 ≤ Real.sin t.angleA := by
  simp only [SphericalTriangle.angleA]
  split_ifs
  · simp
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

/-- sin(angleB) ≥ 0 since angleB ∈ [0, π]. -/
lemma sin_angleB_nonneg (t : SphericalTriangle) : 0 ≤ Real.sin t.angleB := by
  simp only [SphericalTriangle.angleB]
  split_ifs
  · simp
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

-- ============================================================================
-- Part IV: Angle Formulas from Spherical Law of Cosines
-- ============================================================================

/-- Cauchy-Schwarz bound for the argument of arccos in angleA.
    The normalized inner product lies in [-1, 1]. -/
private lemma arg_angleA_bounds (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    -1 ≤ @inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A) /
        (‖projectPerp t.B t.A‖ * ‖projectPerp t.C t.A‖) ∧
    @inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A) /
        (‖projectPerp t.B t.A‖ * ‖projectPerp t.C t.A‖) ≤ 1 := by
  rw [norm_proj_BA, norm_proj_CA]
  have h_prod : 0 < Real.sin t.sideC * Real.sin t.sideB := mul_pos hc hb
  have h_cs := abs_real_inner_le_norm (projectPerp t.B t.A) (projectPerp t.C t.A)
  rw [norm_proj_BA, norm_proj_CA] at h_cs
  rw [abs_le] at h_cs
  constructor
  · rw [le_div_iff₀ h_prod]; linarith [h_cs.1]
  · rw [div_le_one h_prod]; linarith [h_cs.2]

/-- cos(angleA) = (cos(a) - cos(b)cos(c)) / (sin(b)sin(c)) when sin(b), sin(c) > 0. -/
lemma cos_angleA (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.cos t.angleA =
      (Real.cos t.sideA - Real.cos t.sideB * Real.cos t.sideC) /
      (Real.sin t.sideB * Real.sin t.sideC) := by
  simp only [SphericalTriangle.angleA]
  rw [norm_proj_BA, norm_proj_CA]
  have hne_c : Real.sin t.sideC ≠ 0 := ne_of_gt hc
  have hne_b : Real.sin t.sideB ≠ 0 := ne_of_gt hb
  simp only [ne_eq, hne_c, hne_b, or_self, ↓reduceIte, not_false_eq_true]
  have hbounds := arg_angleA_bounds t hb hc
  rw [norm_proj_BA, norm_proj_CA] at hbounds
  rw [Real.cos_arccos hbounds.1 hbounds.2, proj_inner_eq]
  ring

/-- Cauchy-Schwarz bound for the argument of arccos in angleB. -/
private lemma arg_angleB_bounds (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hc : 0 < Real.sin t.sideC) :
    -1 ≤ @inner ℝ Vec3 _ (projectPerp t.A t.B) (projectPerp t.C t.B) /
        (‖projectPerp t.A t.B‖ * ‖projectPerp t.C t.B‖) ∧
    @inner ℝ Vec3 _ (projectPerp t.A t.B) (projectPerp t.C t.B) /
        (‖projectPerp t.A t.B‖ * ‖projectPerp t.C t.B‖) ≤ 1 := by
  rw [norm_proj_AB, norm_proj_CB]
  have h_prod : 0 < Real.sin t.sideC * Real.sin t.sideA := mul_pos hc ha
  have h_cs := abs_real_inner_le_norm (projectPerp t.A t.B) (projectPerp t.C t.B)
  rw [norm_proj_AB, norm_proj_CB] at h_cs
  rw [abs_le] at h_cs
  constructor
  · rw [le_div_iff₀ h_prod]; linarith [h_cs.1]
  · rw [div_le_one h_prod]; linarith [h_cs.2]

/-- cos(angleB) = (cos(b) - cos(a)cos(c)) / (sin(a)sin(c)) when sin(a), sin(c) > 0. -/
lemma cos_angleB (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hc : 0 < Real.sin t.sideC) :
    Real.cos t.angleB =
      (Real.cos t.sideB - Real.cos t.sideA * Real.cos t.sideC) /
      (Real.sin t.sideA * Real.sin t.sideC) := by
  simp only [SphericalTriangle.angleB]
  rw [norm_proj_AB, norm_proj_CB]
  have hne_a : Real.sin t.sideA ≠ 0 := ne_of_gt ha
  have hne_c : Real.sin t.sideC ≠ 0 := ne_of_gt hc
  simp only [ne_eq, hne_a, hne_c, or_self, ↓reduceIte, not_false_eq_true]
  have hbounds := arg_angleB_bounds t ha hc
  rw [norm_proj_AB, norm_proj_CB] at hbounds
  rw [Real.cos_arccos hbounds.1 hbounds.2, proj_inner_eq_B]
  ring

-- ============================================================================
-- Part V: sin²(angle)·sin²(sides) = gramDet
-- ============================================================================

/-- sin²(A)·sin²(b)·sin²(c) = gramDet.
    Follows from substituting cos(A) = (cos(a)-cos(b)cos(c))/(sin(b)sin(c)). -/
lemma sinA_sq_times_bc (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.sin t.angleA ^ 2 * (Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2) =
    gramDet t := by
  have hcA := cos_angleA t hb hc
  have hsin_sq : Real.sin t.angleA ^ 2 = 1 - Real.cos t.angleA ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t.angleA]
  rw [hsin_sq, hcA, gramDet_expand]
  have hbc : Real.sin t.sideB * Real.sin t.sideC ≠ 0 :=
    mul_ne_zero (ne_of_gt hb) (ne_of_gt hc)
  field_simp

/-- sin²(B)·sin²(a)·sin²(c) = gramDet.
    By symmetric reasoning with vertices A and B swapped. -/
lemma sinB_sq_times_ac (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hc : 0 < Real.sin t.sideC) :
    Real.sin t.angleB ^ 2 * (Real.sin t.sideA ^ 2 * Real.sin t.sideC ^ 2) =
    gramDet t := by
  have hcB := cos_angleB t ha hc
  have hsin_sq : Real.sin t.angleB ^ 2 = 1 - Real.cos t.angleB ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t.angleB]
  rw [hsin_sq, hcB, gramDet_expand]
  have hac : Real.sin t.sideA * Real.sin t.sideC ≠ 0 :=
    mul_ne_zero (ne_of_gt ha) (ne_of_gt hc)
  field_simp
  -- Goal after field_simp: sin²b·sin²c - (cos(a)-cos(b)cos(c))² = sin²a·sin²c - (cos(b)-cos(a)cos(c))²
  -- ... both equal G = 1-p²-q²-r²+2pqr
  simp only [Real.sin_sq]
  ring

-- ============================================================================
-- Part VI: Main Theorems
-- ============================================================================

/-- **Spherical Law of Sines** (multiplicative form):
    For a non-degenerate spherical triangle,
    sin(sideA)·sin(angleB) = sin(sideB)·sin(angleA). -/
theorem spherical_law_of_sines_mul (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA)
    (hb : 0 < Real.sin t.sideB)
    (hc : 0 < Real.sin t.sideC) :
    Real.sin t.sideA * Real.sin t.angleB =
    Real.sin t.sideB * Real.sin t.angleA := by
  have hA_nn := sin_angleA_nonneg t
  have hB_nn := sin_angleB_nonneg t
  -- sin²A·sin²b·sin²c = G = sin²B·sin²a·sin²c
  have hA := sinA_sq_times_bc t hb hc
  have hB := sinB_sq_times_ac t ha hc
  -- Cancel sin²c to get sin²A·sin²b = sin²B·sin²a
  have h_sq_eq : Real.sin t.angleA ^ 2 * Real.sin t.sideB ^ 2 =
      Real.sin t.angleB ^ 2 * Real.sin t.sideA ^ 2 := by
    have hc_pos : 0 < Real.sin t.sideC ^ 2 := sq_pos_of_pos hc
    nlinarith
  -- sin(A)·sin(b) = sin(B)·sin(a) from squared equality + non-negativity
  nlinarith [sq_nonneg (Real.sin t.angleA * Real.sin t.sideB - Real.sin t.angleB * Real.sin t.sideA),
             sq_nonneg (Real.sin t.angleA * Real.sin t.sideB + Real.sin t.angleB * Real.sin t.sideA),
             mul_nonneg hA_nn hb.le, mul_nonneg hB_nn ha.le]

/-- **Spherical Law of Sines** (ratio form):
    sin(a)/sin(A) = sin(b)/sin(B) when sin(A), sin(B) > 0. -/
theorem spherical_law_of_sines (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA)
    (hb : 0 < Real.sin t.sideB)
    (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA)
    (hB : 0 < Real.sin t.angleB) :
    Real.sin t.sideA / Real.sin t.angleA =
    Real.sin t.sideB / Real.sin t.angleB := by
  rw [div_eq_div_iff (ne_of_gt hA) (ne_of_gt hB)]
  have := spherical_law_of_sines_mul t ha hb hc
  linarith

/-- The common value: sin(a)/sin(A) equals sin(b)/sin(B) equals sin(c)/sin(C).
    All three ratios are equal. -/
theorem spherical_law_of_sines_all (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA)
    (hb : 0 < Real.sin t.sideB)
    (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA)
    (hB : 0 < Real.sin t.angleB)
    (hC : 0 < Real.sin t.angleC) :
    Real.sin t.sideA / Real.sin t.angleA =
    Real.sin t.sideB / Real.sin t.angleB ∧
    Real.sin t.sideA / Real.sin t.angleA =
    Real.sin t.sideC / Real.sin t.angleC := by
  constructor
  · exact spherical_law_of_sines t ha hb hc hA hB
  · -- For A=C: use the permuted triangle {A:=t.C, B:=t.A, C:=t.B}
    -- In that triangle: sideA_perm = arcLength t.A t.B = t.sideC
    --                   sideB_perm = arcLength t.C t.B = t.sideA (via comm)
    --                   angleA_perm = angleC (of original, at vertex t.C)
    --                   angleB_perm = angleA (of original, at vertex t.A)
    -- We apply spherical_law_of_sines_mul to the permuted triangle.
    set t' : SphericalTriangle := { A := t.C, B := t.A, C := t.B, hA := t.hC, hB := t.hA, hC := t.hB }
    have h_perm : Real.sin t'.sideA * Real.sin t'.angleB =
        Real.sin t'.sideB * Real.sin t'.angleA := by
      apply spherical_law_of_sines_mul
      · -- sin(t'.sideA) > 0: t'.sideA = arcLength A B = t.sideC
        show 0 < Real.sin (arcLength t.A t.B)
        exact hc
      · -- sin(t'.sideB) > 0: t'.sideB = arcLength C B = arcLength B C ... wait
        -- t'.sideB = arcLength t'.A t'.C = arcLength t.C t.B = arcLength B C (via comm)
        show 0 < Real.sin (arcLength t.C t.B)
        rwa [arcLength_comm]
      · -- sin(t'.sideC) > 0: t'.sideC = arcLength t'.A t'.B = arcLength t.C t.A
        show 0 < Real.sin (arcLength t.C t.A)
        rwa [arcLength_comm]
    -- Translate t' angles/sides back to t.
    --   t'.sideA = arcLength t.A t.B = t.sideC                 (definitional)
    --   t'.sideB = arcLength t.C t.B; sin t'.sideB = sin t.sideA via arcLength_comm
    --   t'.angleA = t.angleC                                   (ite vs dite, same body)
    --   t'.angleB = t.angleA                                   (Or.comm + inner_comm + mul_comm)
    have h_sideA : t'.sideA = t.sideC := rfl
    have h_sin_sideB : Real.sin t'.sideB = Real.sin t.sideA := by
      show Real.sin (arcLength t.C t.B) = Real.sin (arcLength t.B t.C)
      rw [arcLength_comm]
    have h_angA : t'.angleA = t.angleC := by
      show
        (if ‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B t.C‖ = 0 then (0 : ℝ)
          else Real.arccos
            ((@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C)) /
              (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖))) =
        (if h : ‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B t.C‖ = 0 then (0 : ℝ)
          else Real.arccos
            ((@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C)) /
              (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖)))
      by_cases hh : ‖projectPerp t.A t.C‖ = 0 ∨ ‖projectPerp t.B t.C‖ = 0
      · rw [if_pos hh, dif_pos hh]
      · rw [if_neg hh, dif_neg hh]
    have h_angB : t'.angleB = t.angleA := by
      show
        (if ‖projectPerp t.C t.A‖ = 0 ∨ ‖projectPerp t.B t.A‖ = 0 then (0 : ℝ)
          else Real.arccos
            ((@inner ℝ Vec3 _ (projectPerp t.C t.A) (projectPerp t.B t.A)) /
              (‖projectPerp t.C t.A‖ * ‖projectPerp t.B t.A‖))) =
        (if ‖projectPerp t.B t.A‖ = 0 ∨ ‖projectPerp t.C t.A‖ = 0 then (0 : ℝ)
          else Real.arccos
            ((@inner ℝ Vec3 _ (projectPerp t.B t.A) (projectPerp t.C t.A)) /
              (‖projectPerp t.B t.A‖ * ‖projectPerp t.C t.A‖)))
      by_cases h1 : ‖projectPerp t.C t.A‖ = 0
      · rw [if_pos (Or.inl h1), if_pos (Or.inr h1)]
      · by_cases h2 : ‖projectPerp t.B t.A‖ = 0
        · rw [if_pos (Or.inr h2), if_pos (Or.inl h2)]
        · rw [if_neg (not_or.mpr ⟨h1, h2⟩), if_neg (not_or.mpr ⟨h2, h1⟩),
              real_inner_comm (projectPerp t.C t.A) (projectPerp t.B t.A),
              mul_comm ‖projectPerp t.C t.A‖ ‖projectPerp t.B t.A‖]
    rw [div_eq_div_iff (ne_of_gt hA) (ne_of_gt hC)]
    rw [h_sideA, h_angA, h_angB, h_sin_sideB] at h_perm
    linarith

-- ============================================================================
-- Part VII: Corollaries
-- ============================================================================

/-- In a non-degenerate spherical triangle, if sin(A) > 0 then G > 0. -/
lemma gramDet_pos_of_sinA_pos (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA) : 0 < gramDet t := by
  have h := sinA_sq_times_bc t hb hc
  have hbc_pos : 0 < Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2 :=
    mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hc)
  nlinarith [sq_pos_of_pos hA]

/-- When G > 0, sin(A) > 0 (the angle is non-degenerate). -/
lemma sinA_pos_of_gramDet_pos (t : SphericalTriangle)
    (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC)
    (hG : 0 < gramDet t) : 0 < Real.sin t.angleA := by
  have h := sinA_sq_times_bc t hb hc
  have hbc_pos : 0 < Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2 :=
    mul_pos (sq_pos_of_pos hb) (sq_pos_of_pos hc)
  have hA_sq_pos : 0 < Real.sin t.angleA ^ 2 := by
    have key : 0 < Real.sin t.angleA ^ 2 * (Real.sin t.sideB ^ 2 * Real.sin t.sideC ^ 2) := h ▸ hG
    exact (mul_pos_iff.mp key).elim (fun hh => hh.1) (fun hh => absurd hbc_pos (not_lt.mpr hh.2.le))
  exact Real.sqrt_pos.mpr hA_sq_pos |>.trans_le (by nlinarith [Real.sqrt_sq (sin_angleA_nonneg t)])

/-- Equilateral triangles (a = b = c) have equal angles (A = B = C). -/
theorem equilateral_angles_equal (t : SphericalTriangle)
    (h_eq : t.sideA = t.sideB)
    (ha : 0 < Real.sin t.sideA)
    (hb : 0 < Real.sin t.sideB)
    (hc : 0 < Real.sin t.sideC) :
    Real.sin t.angleA = Real.sin t.angleB := by
  have := spherical_law_of_sines_mul t ha hb hc
  rw [h_eq] at this
  exact mul_left_cancel₀ (ne_of_gt hb) (by linarith)

end LawOfCosinesOQ01OQ02
