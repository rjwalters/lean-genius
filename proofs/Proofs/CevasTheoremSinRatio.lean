import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-
# Spherical Ceva: The Sin-Ratio Formula for Unit Vectors

## What This Proves

For the spherical Ceva theorem, the key algebraic ingredient is:

If D = (1/‖αB + βC‖) • (αB + βC) is a unit vector on the arc between unit
vectors B and C (with α, β > 0), then:

  sin(arcDist B D) / sin(arcDist D C) = β / α

where arcDist(u, v) = arccos(⟨u, v⟩) is the geodesic arc length.

## Mathematical Significance

This bridges the algebraic spherical Ceva (CevasTheoremOQ02.lean) with a
vector-geometric proof. The full spherical Ceva theorem:

  Concurrent geodesic cevians iff sin(BD)/sin(DC)·sin(CE)/sin(EA)·sin(AF)/sin(FB) = 1

follows immediately from the weight balance βD·βE·βF = αD·αE·αF.

## Proof Idea

In any real inner product space (no Riemannian manifolds needed!):
1. D = (1/n)·(αB + βC) → inner(B, D) = (α + β·m)/n, where m = ⟨B,C⟩, n = ‖αB+βC‖
2. Key identity: 1 - inner(B,D)² = β²(1-m²)/n²
3. sin(arccos x) = √(1-x²) gives sin(BD) = β√(1-m²)/n
4. Similarly sin(DC) = α√(1-m²)/n, so ratio = β/α
-/

namespace CevasTheoremSinRatio

open Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Spherical Ceva Sin-Ratio Formula**

    For unit vectors B, C in a real inner product space, with
      D = (1 / ‖αB + βC‖) • (αB + βC)  (normalized weighted midpoint),
    α, β > 0, and inner(B,C) ≠ ±1 (B, C are not antipodal/identical):

      sin(arccos(inner B D)) / sin(arccos(inner D C)) = β / α

    **Proof**: Direct inner product computation.
    1. inner(B,D) = (α + βm)/n, inner(D,C) = (αm + β)/n (where m = inner B C)
    2. 1 - ((α+βm)/n)² = β²(1-m²)/n² [key algebraic identity, proved by ring after n²=α²+2αβm+β²]
    3. sin(arccos(inner B D)) = β√(1-m²)/n [using sin(arccos x) = √(1-x²)]
    4. Ratio = β/α [cancel √(1-m²)/n]

    No Riemannian manifold theory needed — pure real inner product algebra! -/
theorem sin_ratio_spherical_ceva
    (B C : V) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hB : ‖B‖ = 1) (hC : ‖C‖ = 1)
    (hBC_ne : α • B + β • C ≠ 0)
    (hm_ne_one : inner (𝕜 := ℝ) B C ≠ 1)
    (hm_ne_neg_one : inner (𝕜 := ℝ) B C ≠ -1) :
    Real.sin (Real.arccos (inner (𝕜 := ℝ) B ((1 / ‖α • B + β • C‖) • (α • B + β • C)))) /
    Real.sin (Real.arccos (inner (𝕜 := ℝ) ((1 / ‖α • B + β • C‖) • (α • B + β • C)) C)) =
    β / α := by
  set m := inner (𝕜 := ℝ) B C with hm_def
  set n := ‖α • B + β • C‖ with hn_def
  -- Positivity
  have hn_pos : 0 < n := norm_pos_iff.mpr hBC_ne
  have hn_ne : n ≠ 0 := hn_pos.ne'
  -- Boundary conditions on m
  have hm_le_one : m ≤ 1 := by
    have h : 0 ≤ ‖B - C‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, hB, hC] at h; linarith
  have hm_ge_neg : -1 ≤ m := by
    have h : 0 ≤ ‖B + C‖ ^ 2 := sq_nonneg _
    rw [norm_add_sq_real, hB, hC] at h; linarith
  have hm_lt_one : m < 1 := lt_of_le_of_ne hm_le_one hm_ne_one
  have hm_gt_neg : -1 < m :=
    lt_of_le_of_ne hm_ge_neg (Ne.symm hm_ne_neg_one)
  have h_one_m_sq : 0 < 1 - m ^ 2 := by nlinarith
  -- n² formula
  have hBB : inner (𝕜 := ℝ) B B = 1 := by
    rw [real_inner_self_eq_norm_sq, hB]; norm_num
  have hCC : inner (𝕜 := ℝ) C C = 1 := by
    rw [real_inner_self_eq_norm_sq, hC]; norm_num
  have hn_sq : n ^ 2 = α ^ 2 + 2 * α * β * m + β ^ 2 := by
    -- Use norm_add_sq_real to avoid inner_smul_left (which introduces starRingEnd)
    have expand : n ^ 2 = ‖α • B‖ ^ 2 + 2 * inner (𝕜 := ℝ) (α • B) (β • C) + ‖β • C‖ ^ 2 := by
      rw [← norm_add_sq_real, hn_def]
    have inner_term : inner (𝕜 := ℝ) (α • B) (β • C) = α * β * m := by
      -- Use real_inner_comm without explicit args (matches Docker Mathlib API)
      rw [real_inner_comm, inner_smul_right, real_inner_comm, inner_smul_right, ← hm_def]
      ring
    rw [expand, inner_term, norm_smul, norm_smul, hB, hC]
    simp only [mul_one, Real.norm_of_nonneg hα.le, Real.norm_of_nonneg hβ.le]
    ring
  have hn_sq_ne : n ^ 2 ≠ 0 := (pow_pos hn_pos 2).ne'
  -- Inner product computations (explicit rewrites avoid starRingEnd issues)
  have inner_BD : inner (𝕜 := ℝ) B ((1 / n) • (α • B + β • C)) = (α + β * m) / n := by
    rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
        hBB, ← hm_def]
    ring
  have inner_DC : inner (𝕜 := ℝ) ((1 / n) • (α • B + β • C)) C = (α * m + β) / n := by
    -- Use real_inner_comm to flip (avoids inner_smul_left/starRingEnd), then inner_smul_right
    rw [real_inner_comm, inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right]
    -- Goal: (1/n) * (α * ⟪C, B⟫_ℝ + β * ⟪C, C⟫_ℝ) = (α * m + β) / n
    rw [real_inner_comm, ← hm_def, hCC]
    ring
  -- Key algebraic identity
  have key_BD : n ^ 2 - (α + β * m) ^ 2 = β ^ 2 * (1 - m ^ 2) := by
    rw [hn_sq]; ring
  have key_DC : n ^ 2 - (α * m + β) ^ 2 = α ^ 2 * (1 - m ^ 2) := by
    rw [hn_sq]; ring
  -- sin(arccos(inner B D)) = β * √(1-m²) / n
  have hsin_BD : Real.sin (Real.arccos (inner (𝕜 := ℝ) B ((1 / n) • (α • B + β • C)))) =
      β * Real.sqrt (1 - m ^ 2) / n := by
    rw [inner_BD, Real.sin_arccos]
    have harg : 1 - ((α + β * m) / n) ^ 2 = (β / n) ^ 2 * (1 - m ^ 2) := by
      field_simp [hn_ne]
      nlinarith [key_BD]
    rw [harg, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (div_nonneg hβ.le hn_pos.le)]
    ring
  -- sin(arccos(inner D C)) = α * √(1-m²) / n
  have hsin_DC : Real.sin (Real.arccos (inner (𝕜 := ℝ) ((1 / n) • (α • B + β • C)) C)) =
      α * Real.sqrt (1 - m ^ 2) / n := by
    rw [inner_DC, Real.sin_arccos]
    have harg : 1 - ((α * m + β) / n) ^ 2 = (α / n) ^ 2 * (1 - m ^ 2) := by
      field_simp [hn_ne]
      nlinarith [key_DC]
    rw [harg, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (div_nonneg hα.le hn_pos.le)]
    ring
  -- Compute ratio: (β√(1-m²)/n) / (α√(1-m²)/n) = β/α
  rw [hsin_BD, hsin_DC]
  have hsqrt_ne : Real.sqrt (1 - m ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr h_one_m_sq).ne'
  field_simp [hn_ne, hsqrt_ne, hα.ne', hβ.ne']

end CevasTheoremSinRatio
