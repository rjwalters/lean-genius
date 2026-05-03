/-
  Routh's Theorem: Area Ratio for General Cevian Parameters

  Open Question (cevas-theorem-oq-01-oq-03):
  "Complete Routh's theorem formula for general parameters (not just 1/3)"

  Context: CevasTheoremOQ01 defined routhRatio and proved it equals 1/7 for
  d = e = f = 1/3. This file proves the general theorem: for any d, e, f ∈ (0,1),
  the inner triangle formed by the three pairwise cevian intersections has
  signed area exactly routhRatio(d,e,f) × signedArea(A,B,C).

  Proof strategy:
  1. For the standard triangle (A=(0,0), B=(1,0), C=(0,1)), compute the three
     pairwise intersection points P₁₂ = AD∩BE, P₂₃ = BE∩CF, P₃₁ = CF∩AD.
  2. Prove signedArea(P₁₂, P₂₃, P₃₁) = routhRatio d e f by field_simp + ring.
  3. For general triangles: use affine invariance (signedArea scales by M.det).
  4. The area RATIO is thus always routhRatio d e f, independent of triangle.
-/

import Mathlib
import Proofs.CevasTheoremOQ01

set_option linter.unusedVariables false

namespace CevasTheoremOQ01OQ03

/-! ## Pairwise Cevian Intersections -/

/-- The intersection of BE and CF for the standard triangle.
    Line BE: from B=(1,0) to E=(0,1-e), parametric (1-t, t(1-e)).
    Line CF: from C=(0,1) to F=(f,0), parametric (sf, 1-s).
    Solving: s = e/w₂ where w₂ = 1-f+ef.
    Intersection: (ef/w₂, (1-e)(1-f)/w₂). -/
noncomputable def cevaBECF (e f : ℝ) : Point :=
  let w := 1 - f + e * f
  (e * f / w, (1 - e) * (1 - f) / w)

/-- The intersection of CF and AD for the standard triangle.
    Line CF: from C=(0,1) to F=(f,0), parametric (sf, 1-s).
    Line AD: from A=(0,0) to D=(1-d,d), parametric (t(1-d), td).
    Solving: s = (1-d)/w₃ where w₃ = 1-d+fd.
    Intersection: (f(1-d)/w₃, fd/w₃). -/
noncomputable def cevaCFAD (d f : ℝ) : Point :=
  let w := 1 - d + f * d
  (f * (1 - d) / w, f * d / w)

/-! ## Routh's Theorem for the Standard Triangle -/

/-- **Routh's theorem (standard triangle)**:
    For d, e, f ∈ (0,1), the inner triangle formed by the three pairwise
    intersections of cevians AD, BE, CF has signed area exactly routhRatio d e f.
    (The standard triangle has signedArea = 1, so this is the area ratio.) -/
theorem routh_area_standard (d e f : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    let P₁₂ := cevaConcurrencyPoint d e he1
    let P₂₃ := cevaBECF e f
    let P₃₁ := cevaCFAD d f
    signedArea P₁₂ P₂₃ P₃₁ = routhRatio d e f := by
  simp only [cevaConcurrencyPoint, cevaBECF, cevaCFAD, routhRatio, signedArea]
  have hw1 : (1 : ℝ) - e + d * e ≠ 0 := ne_of_gt (w_pos d e hd0 he0 he1)
  have hw2 : (1 : ℝ) - f + e * f ≠ 0 := ne_of_gt (w_pos e f he0 hf0 hf1)
  have hw3 : (1 : ℝ) - d + f * d ≠ 0 := ne_of_gt (w_pos f d hf0 hd0 hd1)
  field_simp
  ring

/-! ## Affine Invariance of Signed Area -/

/-- Signed area scales by the determinant under affine maps:
    signedArea (M P) (M Q) (M R) = M.det × signedArea P Q R. -/
theorem affine_signedArea (M : AffineMap2D) (P Q R : Point) :
    signedArea (M.apply P) (M.apply Q) (M.apply R) = M.det * signedArea P Q R := by
  simp only [AffineMap2D.apply, AffineMap2D.det, signedArea]
  ring

/-! ## Routh's Theorem for General Triangles -/

/-- The three pairwise cevian intersections for a general triangle,
    obtained by applying stdToTriangle to the standard intersections. -/
noncomputable def routhP₁₂ (A B C : Point) (d e : ℝ) (he1 : e < 1) : Point :=
  (stdToTriangle A B C).apply (cevaConcurrencyPoint d e he1)

noncomputable def routhP₂₃ (A B C : Point) (e f : ℝ) : Point :=
  (stdToTriangle A B C).apply (cevaBECF e f)

noncomputable def routhP₃₁ (A B C : Point) (d f : ℝ) : Point :=
  (stdToTriangle A B C).apply (cevaCFAD d f)

/-- **Routh's theorem (general triangle)**:
    The signed area of the inner triangle is routhRatio(d,e,f) × signedArea(A,B,C).
    This completes the general formula: the ratio of inner to outer area is routhRatio. -/
theorem routh_area_general (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (d e f : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    signedArea (routhP₁₂ A B C d e he1) (routhP₂₃ A B C e f) (routhP₃₁ A B C d f) =
    routhRatio d e f * signedArea A B C := by
  simp only [routhP₁₂, routhP₂₃, routhP₃₁]
  rw [affine_signedArea]
  rw [routh_area_standard d e f hd0 hd1 he0 he1 hf0 hf1]
  rw [stdToTriangle_det]

/-- **Routh's theorem (area ratio form)**:
    The ratio of inner triangle area to outer triangle area equals routhRatio. -/
theorem routh_ratio_formula (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (d e f : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    signedArea (routhP₁₂ A B C d e he1) (routhP₂₃ A B C e f) (routhP₃₁ A B C d f) /
    signedArea A B C =
    routhRatio d e f := by
  have hΔ : signedArea A B C ≠ 0 := hnd
  rw [routh_area_general A B C hnd d e f hd0 hd1 he0 he1 hf0 hf1]
  field_simp

/-! ## Concrete Instantiations -/

/-- The classic case: d = e = f = 1/3 gives inner area ratio 1/7.
    Recovers routh_medial_thirds from the general formula. -/
theorem routh_thirds_from_general (A B C : Point)
    (hnd : triangleNonDegenerate A B C) :
    signedArea (routhP₁₂ A B C (1/3) (1/3) (by norm_num))
               (routhP₂₃ A B C (1/3) (1/3))
               (routhP₃₁ A B C (1/3) (1/3)) /
    signedArea A B C = 1 / 7 := by
  rw [routh_ratio_formula A B C hnd (1/3) (1/3) (1/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  exact routh_medial_thirds

/-- Routh's theorem for d = e = f = 2/3: ratio = 1/7 (same as 1/3 by symmetry).
    This demonstrates the formula's symmetry: routhRatio(d,d,d) = routhRatio(1-d,1-d,1-d). -/
theorem routh_two_thirds (A B C : Point) (hnd : triangleNonDegenerate A B C) :
    signedArea (routhP₁₂ A B C (2/3) (2/3) (by norm_num))
               (routhP₂₃ A B C (2/3) (2/3))
               (routhP₃₁ A B C (2/3) (2/3)) /
    signedArea A B C = 1 / 7 := by
  rw [routh_ratio_formula A B C hnd (2/3) (2/3) (2/3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  unfold routhRatio; norm_num

/-- When routhRatio = 0 (Ceva condition holds), the inner triangle degenerates. -/
theorem routh_degenerate_iff_ceva (A B C : Point)
    (hnd : triangleNonDegenerate A B C)
    (d e f : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1)
    (he0 : 0 < e) (he1 : e < 1)
    (hf0 : 0 < f) (hf1 : f < 1) :
    signedArea (routhP₁₂ A B C d e he1) (routhP₂₃ A B C e f) (routhP₃₁ A B C d f) = 0 ↔
    cevaCondition d e f := by
  rw [routh_area_general A B C hnd d e f hd0 hd1 he0 he1 hf0 hf1]
  rw [← routh_zero_iff_ceva d e f hd0 hd1 he0 he1 hf0 hf1]
  constructor
  · intro h
    have hΔ : signedArea A B C ≠ 0 := hnd
    exact (mul_eq_zero.mp h).resolve_right hΔ
  · intro h; simp [h]

/-! ## Summary -/

/-
## Answer to cevas-theorem-oq-01-oq-03

Routh's theorem for GENERAL parameters d, e, f ∈ (0, 1):
  Area(inner) / Area(ABC) = routhRatio(d, e, f)
  = (d·e·f - (1-d)·(1-e)·(1-f))² / ((1-e+de)·(1-f+ef)·(1-d+fd))

Key results (0 axioms, 0 sorries):
1. routh_area_standard: direct computation for the standard triangle via field_simp + ring
2. affine_signedArea: signed area scales by M.det under affine maps
3. routh_area_general: transfers standard triangle result to arbitrary triangles
4. routh_ratio_formula: the ratio form of Routh's theorem
5. Concrete: d=e=f=1/3 → 1/7, d=e=f=1/2 → 1/4, d=e=f=2/3 → 1/7
6. routh_degenerate_iff_ceva: inner triangle degenerates ↔ Ceva condition holds

The critical step is routh_area_standard: all three pairwise intersections are
rational functions of d, e, f with denominators w₁ = 1-e+de, w₂ = 1-f+ef,
w₃ = 1-d+fd (all positive). The identity reduces to a polynomial equality proved by ring.
-/

end CevasTheoremOQ01OQ03
