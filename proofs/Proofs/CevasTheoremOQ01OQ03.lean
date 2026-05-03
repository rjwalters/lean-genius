/-
# Ceva's Theorem OQ-01-OQ-03: Routh's Theorem for General Parameters

Routh's theorem extends the 1/3 case of `CevasTheoremOQ01.lean` to arbitrary
parameters d, e, f ∈ (0, 1): the inner triangle formed by three non-concurrent
cevians has signed area equal to routhRatio(d,e,f) times the original.

## Setup (Standard Triangle)

For the standard triangle A=(0,0), B=(1,0), C=(0,1):
- D = affineComb B C d   (on BC)
- E = affineComb C A e   (on CA)
- F = affineComb A B f   (on AB)

The three cevians AD, BE, CF intersect pairwise at:
- P = AD ∩ BE  = ((1-d)(1-e)/w₁, d(1-e)/w₁)      where w₁ = 1-e+de
- Q = BE ∩ CF  = (ef/w₂, (1-e)(1-f)/w₂)            where w₂ = 1-f+ef
- R = CF ∩ AD  = (f(1-d)/w₃, fd/w₃)                where w₃ = 1-d+fd

## Main Result

  signedArea(P, Q, R) = routhRatio(d,e,f) · signedArea(A, B, C)

where routhRatio(d,e,f) = (d·e·f - (1-d)·(1-e)·(1-f))² / (w₁·w₂·w₃)
is defined in CevasTheoremOQ01.lean.

## Status: Verified (0 axioms, 0 sorries)
-/

import Proofs.CevasTheoremOQ01
import Mathlib.Tactic

namespace RouthTheorem

-- Standard triangle vertices
abbrev stdA : Point := (0, 0)
abbrev stdB : Point := (1, 0)
abbrev stdC : Point := (0, 1)

/-══════════════════════════════════════════════════════════════
  PART I: DENOMINATOR POSITIVITY
══════════════════════════════════════════════════════════════-/

/-- w₁ = 1 - e + de > 0 for d, e ∈ (0,1) -/
lemma w₁_pos {d e : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (he0 : 0 < e) (he1 : e < 1) :
    0 < 1 - e + d * e := by nlinarith

/-- w₂ = 1 - f + ef > 0 for e, f ∈ (0,1) -/
lemma w₂_pos {e f : ℝ} (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    0 < 1 - f + e * f := by nlinarith

/-- w₃ = 1 - d + fd > 0 for d, f ∈ (0,1) -/
lemma w₃_pos {d f : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    0 < 1 - d + f * d := by nlinarith

/-══════════════════════════════════════════════════════════════
  PART II: INNER TRIANGLE VERTICES
══════════════════════════════════════════════════════════════-/

/-- P = intersection of cevians AD and BE. -/
noncomputable def stdP (d e : ℝ) : Point :=
  ((1 - d) * (1 - e) / (1 - e + d * e), d * (1 - e) / (1 - e + d * e))

/-- Q = intersection of cevians BE and CF. -/
noncomputable def stdQ (e f : ℝ) : Point :=
  (e * f / (1 - f + e * f), (1 - e) * (1 - f) / (1 - f + e * f))

/-- R = intersection of cevians CF and AD. -/
noncomputable def stdR (d f : ℝ) : Point :=
  (f * (1 - d) / (1 - d + f * d), f * d / (1 - d + f * d))

/-══════════════════════════════════════════════════════════════
  PART III: MEMBERSHIP IN CEVIAN LINES
══════════════════════════════════════════════════════════════-/

/-- P lies on cevian AD (the line from A to D = affineComb B C d). -/
theorem stdP_on_AD {d e : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (he0 : 0 < e) (he1 : e < 1) :
    stdP d e ∈ lineThrough stdA (affineComb stdB stdC d) := by
  have hw : (0 : ℝ) < 1 - e + d * e := w₁_pos hd0 hd1 he0 he1
  simp only [lineThrough, stdP, stdA, stdB, stdC, affineComb, Set.mem_setOf_eq]
  refine ⟨(1 - e) / (1 - e + d * e), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

/-- P lies on cevian BE (the line from B to E = affineComb C A e). -/
theorem stdP_on_BE {d e : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (he0 : 0 < e) (he1 : e < 1) :
    stdP d e ∈ lineThrough stdB (affineComb stdC stdA e) := by
  have hw : (0 : ℝ) < 1 - e + d * e := w₁_pos hd0 hd1 he0 he1
  simp only [lineThrough, stdP, stdA, stdB, stdC, affineComb, Set.mem_setOf_eq]
  refine ⟨d / (1 - e + d * e), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

/-- Q lies on cevian BE (the line from B to E = affineComb C A e). -/
theorem stdQ_on_BE {e f : ℝ} (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    stdQ e f ∈ lineThrough stdB (affineComb stdC stdA e) := by
  have hw : (0 : ℝ) < 1 - f + e * f := w₂_pos he0 he1 hf0 hf1
  simp only [lineThrough, stdQ, stdA, stdB, stdC, affineComb, Set.mem_setOf_eq]
  refine ⟨(1 - f) / (1 - f + e * f), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

/-- Q lies on cevian CF (the line from C to F = affineComb A B f). -/
theorem stdQ_on_CF {e f : ℝ} (he0 : 0 < e) (he1 : e < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    stdQ e f ∈ lineThrough stdC (affineComb stdA stdB f) := by
  have hw : (0 : ℝ) < 1 - f + e * f := w₂_pos he0 he1 hf0 hf1
  simp only [lineThrough, stdQ, stdA, stdB, stdC, affineComb, Set.mem_setOf_eq]
  refine ⟨e / (1 - f + e * f), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

/-- R lies on cevian CF (the line from C to F = affineComb A B f). -/
theorem stdR_on_CF {d f : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    stdR d f ∈ lineThrough stdC (affineComb stdA stdB f) := by
  have hw : (0 : ℝ) < 1 - d + f * d := w₃_pos hd0 hd1 hf0 hf1
  simp only [lineThrough, stdR, stdA, stdB, stdC, affineComb, Set.mem_setOf_eq]
  refine ⟨(1 - d) / (1 - d + f * d), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

/-- R lies on cevian AD (the line from A to D = affineComb B C d). -/
theorem stdR_on_AD {d f : ℝ} (hd0 : 0 < d) (hd1 : d < 1) (hf0 : 0 < f) (hf1 : f < 1) :
    stdR d f ∈ lineThrough stdA (affineComb stdB stdC d) := by
  have hw : (0 : ℝ) < 1 - d + f * d := w₃_pos hd0 hd1 hf0 hf1
  simp only [lineThrough, stdR, stdA, stdB, stdC, affineComb, Set.mem_setOf_eq]
  refine ⟨f / (1 - d + f * d), ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring

/-══════════════════════════════════════════════════════════════
  PART IV: ROUTH'S THEOREM — MAIN FORMULA
══════════════════════════════════════════════════════════════-/

/-- **Routh's Theorem**: For cevian parameters d, e, f ∈ (0,1), the inner
    triangle formed by the three pairwise cevian intersections has signed area
    equal to routhRatio(d,e,f) times the signed area of the standard triangle.

    The proof: all expressions are rational functions of d, e, f; after clearing
    denominators (field_simp) the result reduces to a polynomial identity (ring). -/
theorem routh_theorem_std {d e f : ℝ}
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    signedArea (stdP d e) (stdQ e f) (stdR d f) =
    routhRatio d e f * signedArea stdA stdB stdC := by
  have hw1 : (1 : ℝ) - e + d * e ≠ 0 := ne_of_gt (w₁_pos hd0 hd1 he0 he1)
  have hw2 : (1 : ℝ) - f + e * f ≠ 0 := ne_of_gt (w₂_pos he0 he1 hf0 hf1)
  have hw3 : (1 : ℝ) - d + f * d ≠ 0 := ne_of_gt (w₃_pos hd0 hd1 hf0 hf1)
  simp only [stdP, stdQ, stdR, signedArea, routhRatio, stdA, stdB, stdC]
  field_simp
  ring

/-══════════════════════════════════════════════════════════════
  PART V: COROLLARIES AND APPLICATIONS
══════════════════════════════════════════════════════════════-/

/-- The signed area of the standard triangle is 1. -/
theorem std_signedArea : signedArea stdA stdB stdC = 1 := by
  simp [signedArea, stdA, stdB, stdC]

/-- **Routh's Theorem** (explicit area form): the inner triangle area is
    exactly routhRatio(d,e,f). -/
theorem routh_area_explicit {d e f : ℝ}
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    signedArea (stdP d e) (stdQ e f) (stdR d f) = routhRatio d e f := by
  rw [routh_theorem_std hd0 hd1 he0 he1 hf0 hf1, std_signedArea, mul_one]

/-- **Verification of 1/7 case**: when d = e = f = 1/3, the inner triangle
    has signed area 1/7, recovering the well-known Routh's theorem special case. -/
theorem routh_medial_thirds_area :
    signedArea (stdP (1/3) (1/3)) (stdQ (1/3) (1/3)) (stdR (1/3) (1/3)) = 1/7 := by
  rw [routh_area_explicit (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
  exact routh_medial_thirds

/-- **Routh's Theorem — cevian degeneracy**: if the cevians are concurrent
    (Ceva condition), the inner triangle degenerates to a point (area = 0). -/
theorem routh_concurrent_area_zero {d e f : ℝ}
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1)
    (hceva : cevaCondition d e f) :
    signedArea (stdP d e) (stdQ e f) (stdR d f) = 0 := by
  rw [routh_area_explicit hd0 hd1 he0 he1 hf0 hf1]
  exact (routh_zero_iff_ceva d e f hd0 hd1 he0 he1 hf0 hf1).mpr hceva

/-- The median cevians (d = e = f = 1/2) are concurrent (Ceva condition holds). -/
theorem medians_ceva_condition : cevaCondition (1/2) (1/2) (1/2) := medians_ceva

/-- Midpoint cevians form no inner triangle (confirmed by zero area formula). -/
theorem routh_medians_zero :
    signedArea (stdP (1/2) (1/2)) (stdQ (1/2) (1/2)) (stdR (1/2) (1/2)) = 0 := by
  apply routh_concurrent_area_zero (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact medians_ceva

/-- **Routh's ratio is nonneg** for d, e, f ∈ (0,1): the inner triangle area
    is always nonnegative. -/
theorem routhRatio_nonneg {d e f : ℝ}
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    0 ≤ routhRatio d e f := by
  unfold routhRatio
  apply div_nonneg
  · positivity
  · have hw1 : (0 : ℝ) < 1 - e + d * e := w₁_pos hd0 hd1 he0 he1
    have hw2 : (0 : ℝ) < 1 - f + e * f := w₂_pos he0 he1 hf0 hf1
    have hw3 : (0 : ℝ) < 1 - d + f * d := w₃_pos hd0 hd1 hf0 hf1
    positivity

/-- **Explicit computation**: d=1/2, e=1/3, f=1/4 gives an asymmetric
    configuration. The area ratio is 1/10. -/
theorem routh_asymmetric_example :
    routhRatio (1/2) (1/3) (1/4) = 1 / 10 := by
  unfold routhRatio; norm_num

/-- **Routh ratio for equal-product parameters**: when def = (1-d)(1-e)(1-f),
    the area is 0 and cevians are concurrent (converse of Ceva). -/
theorem routh_zero_iff (d e f : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    routhRatio d e f = 0 ↔ d * e * f = (1 - d) * (1 - e) * (1 - f) := by
  rw [routh_zero_iff_ceva d e f hd0 hd1 he0 he1 hf0 hf1]
  simp [cevaCondition]

end RouthTheorem
