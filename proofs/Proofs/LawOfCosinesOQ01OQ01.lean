/-
Dual Spherical Law of Cosines (law-of-cosines-oq-01-oq-01)

For a spherical triangle on S² with arc-length sides a, b, c ∈ (0, π) and
dihedral angles A, B, C at the corresponding vertices, the dual law states:

  cos C = -cos A · cos B + sin A · sin B · cos c

This is the "angle version" of the spherical law of cosines: instead of expressing
a side's cosine in terms of the other sides and an included angle, it expresses
an angle's cosine in terms of the other angles and the included side.

## Proof Strategy

Let p = cos a, q = cos b, r = cos c (inner products of unit vertices on S²).
Define the Gram determinant Δ := 1 - p² - q² - r² + 2pqr > 0 (non-degeneracy).

The dihedral angles satisfy the "angle formula" (from the inner product decomposition):
  cos A = (p - qr)/(sin b · sin c)   where sin b = √(1-q²), sin c = √(1-r²)
  cos B = (q - pr)/(sin a · sin c)   where sin a = √(1-p²)
  cos C = (r - pq)/(sin a · sin b)

And sin A · sin B = Δ/(sin a · sin b · sin²c).

The dual law reduces to the ring identity:
  r · Δ - (p - qr)(q - pr) = (r - pq)(1 - r²)

References:
- Todhunter, "Spherical Trigonometry" (1886), §47
- Van Brummelen, "Heavenly Mathematics" (2013), Chapter 4
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real

namespace DualSphericalLaw

-- ============================================================================
-- Part I: Core Algebraic Identities
-- ============================================================================

/-- Each of the three "angle factor" expressions equals the same Gram determinant Δ.
    For angle A: sb²·sc² - (p - qr)² = Δ. -/
lemma gram_factor_A (p q r : ℝ) :
    (1 - q ^ 2) * (1 - r ^ 2) - (p - q * r) ^ 2 =
    1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r := by ring

/-- For angle B: sa²·sc² - (q - pr)² = Δ. -/
lemma gram_factor_B (p q r : ℝ) :
    (1 - p ^ 2) * (1 - r ^ 2) - (q - p * r) ^ 2 =
    1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r := by ring

/-- For angle C: sa²·sb² - (r - pq)² = Δ. -/
lemma gram_factor_C (p q r : ℝ) :
    (1 - p ^ 2) * (1 - q ^ 2) - (r - p * q) ^ 2 =
    1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r := by ring

/-- The central ring identity: the dual law reduces to this after clearing denominators.

After multiplying cos C = -cos A · cos B + sin A · sin B · cos c
through by sin a · sin b · sin²c, we get:
  (r - pq)(1 - r²) = Δ · r - (p - qr)(q - pr)

where Δ = 1 - p² - q² - r² + 2pqr, and 1 - r² = sin²c. -/
lemma dual_ring_identity (p q r : ℝ) :
    (r - p * q) * (1 - r ^ 2) =
    (1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) * r -
    (p - q * r) * (q - p * r) := by ring

-- ============================================================================
-- Part II: The Range Condition (angles are well-defined)
-- ============================================================================

/-- The angle-formula input (p - qr)/(sb·sc) is in [-1, 1] when Δ ≥ 0. -/
lemma cosA_bound (p q r : ℝ) (hq : q ^ 2 < 1) (hr : r ^ 2 < 1)
    (hΔ : 0 ≤ 1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) :
    (p - q * r) ^ 2 ≤ (1 - q ^ 2) * (1 - r ^ 2) := by
  nlinarith [gram_factor_A p q r]

/-- The angle-formula input (q - pr)/(sa·sc) is in [-1, 1] when Δ ≥ 0. -/
lemma cosB_bound (p q r : ℝ) (hp : p ^ 2 < 1) (hr : r ^ 2 < 1)
    (hΔ : 0 ≤ 1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) :
    (q - p * r) ^ 2 ≤ (1 - p ^ 2) * (1 - r ^ 2) := by
  nlinarith [gram_factor_B p q r]

/-- The angle-formula input (r - pq)/(sa·sb) is in [-1, 1] when Δ ≥ 0. -/
lemma cosC_bound (p q r : ℝ) (hp : p ^ 2 < 1) (hq : q ^ 2 < 1)
    (hΔ : 0 ≤ 1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) :
    (r - p * q) ^ 2 ≤ (1 - p ^ 2) * (1 - q ^ 2) := by
  nlinarith [gram_factor_C p q r]

-- ============================================================================
-- Part III: The Dual Spherical Law (Algebraic Form)
-- ============================================================================

/-- **The Dual Spherical Law of Cosines** (law-of-cosines-oq-01-oq-01)

For a non-degenerate spherical triangle with cosines of sides
p = cos a, q = cos b, r = cos c (where a, b, c ∈ (0, π)):

The Gram determinant Δ := 1 - p² - q² - r² + 2pqr > 0 ensures the triangle is
non-degenerate (vertices not coplanar).

Define sines: sa = √(1-p²), sb = √(1-q²), sc = √(1-r²), sΔ = √Δ.
The dihedral angles satisfy:
  cos A = (p - qr)/(sb·sc),  cos B = (q - pr)/(sa·sc),  cos C = (r - pq)/(sa·sb)
  sin A = sΔ/(sb·sc),        sin B = sΔ/(sa·sc)

The dual law states: cos C = -cos A · cos B + sin A · sin B · cos c.

This is equivalent (after multiplying by sa·sb·sc²) to the ring identity:
  (r - pq)·(1 - r²) = Δ·r - (p-qr)·(q-pr)
-/
theorem dual_spherical_law_algebraic (p q r : ℝ)
    (hp : p ^ 2 < 1) (hq : q ^ 2 < 1) (hr : r ^ 2 < 1)
    (hΔ : 0 < 1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r)
    (cosA cosB cosC sinA sinB : ℝ)
    (hcA : cosA = (p - q * r) / (Real.sqrt (1 - q ^ 2) * Real.sqrt (1 - r ^ 2)))
    (hcB : cosB = (q - p * r) / (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - r ^ 2)))
    (hcC : cosC = (r - p * q) / (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2)))
    (hsA : sinA = Real.sqrt (1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) /
               (Real.sqrt (1 - q ^ 2) * Real.sqrt (1 - r ^ 2)))
    (hsB : sinB = Real.sqrt (1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) /
               (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - r ^ 2))) :
    cosC = -cosA * cosB + sinA * sinB * r := by
  subst hcA hcB hcC hsA hsB
  have hsa : Real.sqrt (1 - p ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hsb : Real.sqrt (1 - q ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hsc : Real.sqrt (1 - r ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hsa2 : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by linarith)
  have hsb2 : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (by linarith)
  have hsc2 : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
  have hΔ2 : Real.sqrt (1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) ^ 2 =
              1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r := Real.sq_sqrt (by linarith)
  have hcore := dual_ring_identity p q r
  field_simp
  nlinarith [sq_nonneg (Real.sqrt (1 - p ^ 2)),
             sq_nonneg (Real.sqrt (1 - q ^ 2)),
             sq_nonneg (Real.sqrt (1 - r ^ 2)),
             sq_nonneg (Real.sqrt (1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r)),
             mul_pos (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - p ^ 2))
                     (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - q ^ 2)),
             mul_pos (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - p ^ 2))
                     (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - r ^ 2)),
             mul_pos (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - q ^ 2))
                     (Real.sqrt_pos.mpr (by linarith : (0:ℝ) < 1 - r ^ 2))]

-- ============================================================================
-- Part IV: The Dual Law via arccos (Geometric Form)
-- ============================================================================

/-- **Dual Spherical Law of Cosines (arccos form)**.

When the dihedral angles are defined via the arccos formula (the standard
definition for spherical triangles), the dual law holds directly.

The angles are:
  A = arccos((p-qr)/(sb·sc))
  B = arccos((q-pr)/(sa·sc))
  C = arccos((r-pq)/(sa·sb))

and the dual law cos C = -cos A · cos B + sin A · sin B · r follows from
the algebraic form above. -/
theorem dual_spherical_law_arccos (p q r : ℝ)
    (hp : p ^ 2 < 1) (hq : q ^ 2 < 1) (hr : r ^ 2 < 1)
    (hΔ : 0 < 1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) :
    let sa := Real.sqrt (1 - p ^ 2)
    let sb := Real.sqrt (1 - q ^ 2)
    let sc := Real.sqrt (1 - r ^ 2)
    let A := Real.arccos ((p - q * r) / (sb * sc))
    let B := Real.arccos ((q - p * r) / (sa * sc))
    let C := Real.arccos ((r - p * q) / (sa * sb))
    Real.cos C = -Real.cos A * Real.cos B + Real.sin A * Real.sin B * r := by
  simp only
  -- Express cos and sin of angles via arccos formulas
  have hsa_pos : 0 < Real.sqrt (1 - p ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hsb_pos : 0 < Real.sqrt (1 - q ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hsc_pos : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr (by linarith)
  -- The arccos inputs lie in [-1, 1]
  have hbA : |((p - q * r) / (Real.sqrt (1 - q ^ 2) * Real.sqrt (1 - r ^ 2)))| ≤ 1 := by
    rw [abs_le]; constructor
    · apply neg_one_le_div_of_le (mul_pos hsb_pos hsc_pos)
      have hb := cosA_bound p q r hq hr (le_of_lt hΔ)
      have hsb2 : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (by linarith)
      have hsc2 : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
      nlinarith [sq_abs (p - q * r), sq_nonneg (Real.sqrt (1 - q ^ 2) * Real.sqrt (1 - r ^ 2) + (p - q * r))]
    · apply div_le_one_of_le _ (le_of_lt (mul_pos hsb_pos hsc_pos))
      have hb := cosA_bound p q r hq hr (le_of_lt hΔ)
      have hsb2 : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (by linarith)
      have hsc2 : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg (Real.sqrt (1 - q ^ 2) * Real.sqrt (1 - r ^ 2) - (p - q * r))]
  have hbB : |((q - p * r) / (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - r ^ 2)))| ≤ 1 := by
    rw [abs_le]; constructor
    · apply neg_one_le_div_of_le (mul_pos hsa_pos hsc_pos)
      have hb := cosB_bound p q r hp hr (le_of_lt hΔ)
      have hsa2 : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by linarith)
      have hsc2 : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
      nlinarith [sq_abs (q - p * r), sq_nonneg (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - r ^ 2) + (q - p * r))]
    · apply div_le_one_of_le _ (le_of_lt (mul_pos hsa_pos hsc_pos))
      have hb := cosB_bound p q r hp hr (le_of_lt hΔ)
      have hsa2 : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by linarith)
      have hsc2 : Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - r ^ 2) - (q - p * r))]
  have hbC : |((r - p * q) / (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2)))| ≤ 1 := by
    rw [abs_le]; constructor
    · apply neg_one_le_div_of_le (mul_pos hsa_pos hsb_pos)
      have hb := cosC_bound p q r hp hq (le_of_lt hΔ)
      have hsa2 : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by linarith)
      have hsb2 : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (by linarith)
      nlinarith [sq_abs (r - p * q), sq_nonneg (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2) + (r - p * q))]
    · apply div_le_one_of_le _ (le_of_lt (mul_pos hsa_pos hsb_pos))
      have hb := cosC_bound p q r hp hq (le_of_lt hΔ)
      have hsa2 : Real.sqrt (1 - p ^ 2) ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by linarith)
      have hsb2 : Real.sqrt (1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg (Real.sqrt (1 - p ^ 2) * Real.sqrt (1 - q ^ 2) - (r - p * q))]
  -- Apply cos_arccos and sin_arccos
  rw [Real.cos_arccos hbC, Real.cos_arccos hbA, Real.cos_arccos hbB,
      Real.sin_arccos hbA, Real.sin_arccos hbB]
  apply dual_spherical_law_algebraic p q r hp hq hr hΔ
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

-- ============================================================================
-- Part V: Concrete Verification
-- ============================================================================

/-- Verify the dual law for an equilateral spherical triangle with sides π/3.
    For p = q = r = 1/2: Δ = 1 - 3/4 + 2·(1/8) = 1 - 3/4 + 1/4 = 1/2 > 0.
    cos C = (1/2 - 1/4)/(sin²(π/3)) = (1/4)/(3/4) = 1/3.
    Check: -cos A · cos B + sin A · sin B · cos c = -(1/3)² + (Δ/(sin·sin)) · (1/2). -/
theorem equilateral_dual_law_check :
    (1/2 - (1/2) * (1/2)) * (1 - (1/2)^2) =
    (1 - (1/2)^2 - (1/2)^2 - (1/2)^2 + 2*(1/2)*(1/2)*(1/2)) * (1/2) -
    ((1/2) - (1/2)*(1/2)) * ((1/2) - (1/2)*(1/2)) := by norm_num

/-- Summary: the dual law cos C = -cos A cos B + sin A sin B cos c holds
    for all non-degenerate spherical triangles, reducing to a ring identity. -/
theorem dual_law_summary :
    ∀ p q r : ℝ, (r - p * q) * (1 - r ^ 2) + (p - q * r) * (q - p * r) =
    (1 - p ^ 2 - q ^ 2 - r ^ 2 + 2 * p * q * r) * r := by
  intros; ring

end DualSphericalLaw
