/-
  Euler's triangle formula  OI² = R² − 2Rr

  For a triangle with circumcenter `O`, incenter `I`, circumradius `R` and
  inradius `r`, the squared distance between the two centers is

      OI² = R² − 2·R·r,

  Euler's classical relation.  Its immediate corollary `OI² ≥ 0` is Euler's
  inequality `R ≥ 2r`.

  This is the open-question child `oq-06-oq-01` of the Heron's-formula gallery
  entry.  The sibling `oq-06` already established Euler's inequality purely in
  the side-length algebraic model (`R = abc/(4·Area)`, `r = Area/s`).  Here we
  upgrade that to the *genuine geometric* statement: `O` and `I` are honest
  points of a real inner-product space and `OI²` is their honest squared
  Euclidean distance.

  ## Strategy

  Place the circumcenter `O` anywhere and let `u = A−O`, `v = B−O`, `w = C−O`
  be the position vectors of the vertices, all of length `R` (they lie on the
  circumcircle).  The side lengths are `a = |v−w|`, `b = |w−u|`, `c = |u−v|`,
  and the incenter is the barycentric combination

      I = (a·A + b·B + c·C) / (a+b+c).

  The heart of the proof is a pure inner-product identity, requiring no area
  and no square roots:

      ‖a·u + b·v + c·w‖² = R²·(a+b+c)² − abc·(a+b+c),

  obtained by expanding the inner product and using
  `⟪u,v⟫ = R² − c²/2`, etc. (from `|u−v|² = ‖u‖² − 2⟪u,v⟫ + ‖v‖²`).
  Dividing by `(a+b+c)²` gives the clean "Euler core"

      OI² = R² − abc/(a+b+c).

  The bridge to the named `R² − 2Rr` form is the elementary algebraic identity
  `2·R·r = abc/(a+b+c)` (the `Area` cancels), which holds once `R` is the
  circumradius `abc/(4·Area)` from the parent entry.

  Axioms: 0
  Sorries: 0
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Proofs.HeronsFormulaOQ06

namespace EulerTriangleFormulaHeronOQ0601

open scoped InnerProductSpace
open EulerInequalityHeronOQ06

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

-- ════════════════════════════════════════════════════════════════
-- PART I: The inner-product core
-- ════════════════════════════════════════════════════════════════

/-- Expansion of the squared norm of the weighted vertex sum.  For three
    vectors of common length `R`, with pairwise distances `a = |v−w|`,
    `b = |w−u|`, `c = |u−v|`,

        ‖a·u + b·v + c·w‖² = R²·(a+b+c)² − abc·(a+b+c).

    This is the entire geometric content of Euler's theorem; everything else
    is algebra. -/
theorem weighted_sum_norm_sq
    (u v w : F) (R : ℝ)
    (hu : ‖u‖ = R) (hv : ‖v‖ = R) (hw : ‖w‖ = R)
    (a b c : ℝ) (ha : a = ‖v - w‖) (hb : b = ‖w - u‖) (hc : c = ‖u - v‖) :
    ‖a • u + b • v + c • w‖ ^ 2 = R ^ 2 * (a + b + c) ^ 2 - a * b * c * (a + b + c) := by
  -- The three Gram inner products in terms of the sides.
  have huv : ⟪u, v⟫_ℝ = R ^ 2 - c ^ 2 / 2 := by
    have h := norm_sub_sq_real u v
    rw [hu, hv, ← hc] at h
    linarith
  have hvw : ⟪v, w⟫_ℝ = R ^ 2 - a ^ 2 / 2 := by
    have h := norm_sub_sq_real v w
    rw [hv, hw, ← ha] at h
    linarith
  have huw : ⟪u, w⟫_ℝ = R ^ 2 - b ^ 2 / 2 := by
    have h := norm_sub_sq_real w u
    rw [hw, hu, ← hb] at h
    have hcomm := real_inner_comm w u  -- ⟪u, w⟫_ℝ = ⟪w, u⟫_ℝ
    linarith [h, hcomm]
  -- Expand ‖·‖² = ⟪·,·⟫ and reduce to the Gram entries.
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  -- Normalize the reversed Gram entries to the forward orientation.
  rw [real_inner_comm u v, real_inner_comm u w, real_inner_comm v w]
  rw [real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v, real_inner_self_eq_norm_sq w,
      hu, hv, hw, huv, hvw, huw]
  ring

-- ════════════════════════════════════════════════════════════════
-- PART II: The Euler core — OI² = R² − abc/(a+b+c)
-- ════════════════════════════════════════════════════════════════

/-- **Euler core (point form).**  For a triangle `A B C` inscribed in a circle
    of centre `O` and radius `R`, with incenter `I = (a·A+b·B+c·C)/(a+b+c)`
    (barycentric coordinates the side lengths), the squared distance from the
    circumcenter to the incenter is

        OI² = R² − abc/(a+b+c).

    No area or square root enters; this is pure inner-product algebra. -/
theorem incenter_dist_circumcenter_sq
    (O A B C : F) (R : ℝ)
    (hA : dist O A = R) (hB : dist O B = R) (hC : dist O C = R)
    (a b c : ℝ) (ha : a = dist B C) (hb : b = dist C A) (hc : c = dist A B)
    (hpos : 0 < a + b + c)
    (I : F) (hI : I = (a + b + c)⁻¹ • (a • A + b • B + c • C)) :
    dist O I ^ 2 = R ^ 2 - a * b * c / (a + b + c) := by
  have hs : (a + b + c) ≠ 0 := ne_of_gt hpos
  -- Position vectors from the circumcenter.
  set u := A - O with hu_def
  set v := B - O with hv_def
  set w := C - O with hw_def
  have hnu : ‖u‖ = R := by rw [hu_def, ← dist_eq_norm']; exact hA
  have hnv : ‖v‖ = R := by rw [hv_def, ← dist_eq_norm']; exact hB
  have hnw : ‖w‖ = R := by rw [hw_def, ← dist_eq_norm']; exact hC
  have hsa : a = ‖v - w‖ := by
    rw [ha, dist_eq_norm, hv_def, hw_def]; congr 1; abel
  have hsb : b = ‖w - u‖ := by
    rw [hb, dist_eq_norm, hw_def, hu_def]; congr 1; abel
  have hsc : c = ‖u - v‖ := by
    rw [hc, dist_eq_norm, hu_def, hv_def]; congr 1; abel
  -- I − O is the normalized weighted sum of the position vectors.
  have hIO : I - O = (a + b + c)⁻¹ • (a • u + b • v + c • w) := by
    have hsum : a • u + b • v + c • w = (a • A + b • B + c • C) - (a + b + c) • O := by
      rw [hu_def, hv_def, hw_def]; module
    rw [hsum, smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul, hI]
  -- Compute the squared distance.
  rw [dist_eq_norm', hIO, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      weighted_sum_norm_sq u v w R hnu hnv hnw a b c hsa hsb hsc]
  field_simp

-- ════════════════════════════════════════════════════════════════
-- PART III: Bridge to R² − 2Rr and Euler's theorem
-- ════════════════════════════════════════════════════════════════

/-- The algebraic identity `2·R·r = abc/(a+b+c)` in the side-length model
    (the `Area` cancels). -/
theorem two_circumradius_mul_inradius
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    2 * circumradius a b c * inradius a b c = a * b * c / (a + b + c) := by
  have hA : 0 < area a b c := area_pos ha hb hc hab hbc hca
  have habc : (a + b + c) ≠ 0 := by linarith
  unfold circumradius inradius semiperimeter
  field_simp
  ring

/-- **Euler's triangle formula.**  `OI² = R² − 2·R·r`, where `R` is the
    circumradius `abc/(4·Area)` of the triangle with sides `a,b,c` and `r` its
    inradius.  The circumcenter `O`, incenter `I` and vertices `A,B,C` are
    honest points; `OI²` is their honest squared distance. -/
theorem euler_OI_sq
    (O A B C : F) (R : ℝ)
    (hA : dist O A = R) (hB : dist O B = R) (hC : dist O C = R)
    (a b c : ℝ) (ha : a = dist B C) (hb : b = dist C A) (hc : c = dist A B)
    (hap : 0 < a) (hbp : 0 < b) (hcp : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b)
    (I : F) (hI : I = (a + b + c)⁻¹ • (a • A + b • B + c • C))
    (hcirc : R = circumradius a b c) :
    dist O I ^ 2 = R ^ 2 - 2 * R * inradius a b c := by
  have hpos : 0 < a + b + c := by linarith
  rw [incenter_dist_circumcenter_sq O A B C R hA hB hC a b c ha hb hc hpos I hI]
  rw [hcirc, two_circumradius_mul_inradius hap hbp hcp hab hbc hca]

/-- **Euler's inequality, geometrically.**  Because `OI² ≥ 0`, the circumradius
    is at least twice the inradius: `R ≥ 2r`. -/
theorem euler_inequality_of_dist
    (O A B C : F) (R : ℝ)
    (hA : dist O A = R) (hB : dist O B = R) (hC : dist O C = R)
    (a b c : ℝ) (ha : a = dist B C) (hb : b = dist C A) (hc : c = dist A B)
    (hap : 0 < a) (hbp : 0 < b) (hcp : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b)
    (I : F) (hI : I = (a + b + c)⁻¹ • (a • A + b • B + c • C))
    (hcirc : R = circumradius a b c) :
    2 * inradius a b c ≤ R := by
  have hform := euler_OI_sq O A B C R hA hB hC a b c ha hb hc hap hbp hcp hab hbc hca I hI hcirc
  have hRpos : 0 < R := by
    rw [hcirc]; unfold circumradius
    have hA' : 0 < area a b c := area_pos hap hbp hcp hab hbc hca
    positivity
  have hsq : (0 : ℝ) ≤ dist O I ^ 2 := sq_nonneg _
  -- R² − 2Rr = OI² ≥ 0  and  R > 0  ⟹  R ≥ 2r
  nlinarith [hform, hsq, hRpos]

end EulerTriangleFormulaHeronOQ0601
