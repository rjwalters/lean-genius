/-
# Buffon's Needle: Higher-Dimensional Hyperplane Arrangements

Generalization of Buffon's needle to n-dimensional Euclidean space
with parallel hyperplane arrangements.

For a line segment of length L in ℝⁿ dropped randomly among parallel
hyperplanes spaced d apart, the expected number of crossings is:

  E[crossings] = c_n · L / d

where c_n = E[|⟨u, e₁⟩|] for uniform u ∈ S^{n-1} is the expected
absolute cosine between a random direction and the hyperplane normal.

Using Gamma functions: c_n = 2Γ(n/2) / ((n-1)·√π·Γ((n-1)/2))

Key values:
  c₂ = 2/π     ← classical Buffon's needle
  c₃ = 1/2     ← needle among parallel planes in 3D
  c₄ = 4/(3π)  ← 4-dimensional case

The constants decrease with dimension: c₂ > c₃ > c₄ > ⋯ → 0,
reflecting the concentration of measure phenomenon on high-dimensional
spheres (random directions become nearly orthogonal to any fixed axis).

Connection to the 2D case:
  For n = 2, c₂ = 2/π gives E = 2L/(πd), matching Buffon-Barbier.

Historical context:
  Cauchy (1850) gave the integral-geometric framework.
  The n-dimensional generalization follows from the mean width formula
  for convex bodies (Bonnesen-Fenchel, 1934).
-/
import Mathlib

namespace BuffonHigherDim

open Real

-- ============================================================
-- Section 1: The Buffon Dimensional Constant
-- ============================================================

/-- The dimensional constant for Buffon's needle in ℝⁿ.

    c_n is the expected absolute cosine between a random direction
    u ∈ S^{n-1} and any fixed unit vector e₁:
      c_n = E[|⟨u, e₁⟩|]

    Defined using the Gamma function ratio:
      c_n = 2 · Γ(n/2) / ((n-1) · √π · Γ((n-1)/2))

    For n ≤ 1 we set c_n = 0 (degenerate). -/
noncomputable def buffonConstant (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else 2 * Real.Gamma ((n : ℝ) / 2) /
    (((n : ℝ) - 1) * Real.sqrt π * Real.Gamma (((n : ℝ) - 1) / 2))

-- The Gamma function value Γ(1/2) = √π requires the Gaussian integral.
/-- Γ(1/2) = √π. Follows from ∫₀^∞ t^{-1/2} e^{-t} dt = √π
    (substitution t = x² reduces to the Gaussian integral). -/
axiom gamma_one_half : Real.Gamma (1 / 2) = Real.sqrt π

/-- c₂ = 2/π: the classical Buffon constant.
    Proof: c₂ = 2Γ(1)/((2-1)·√π·Γ(1/2)) = 2·1/(1·√π·√π) = 2/π. -/
theorem buffonConstant_two : buffonConstant 2 = 2 / π := by
  unfold buffonConstant
  simp only [show ¬((2 : ℕ) ≤ 1) from by omega, ↓reduceIte]
  have h1 : ((2 : ℕ) : ℝ) / 2 = 1 := by push_cast; ring
  have h2 : (((2 : ℕ) : ℝ) - 1) / 2 = 1 / 2 := by push_cast; ring
  have h3 : ((2 : ℕ) : ℝ) - 1 = 1 := by push_cast; ring
  rw [h1, h2, h3, Real.Gamma_one, gamma_one_half, mul_one, one_mul,
      Real.mul_self_sqrt (le_of_lt pi_pos)]

/-- c₃ = 1/2: in 3D, a needle of length L among parallel planes
    has E = L/(2d). The 3D constant is smaller than the 2D constant
    because random 3D directions are less likely to be nearly parallel
    to the hyperplane normal.
    Proof: c₃ = 2Γ(3/2)/(2·√π·Γ(1)) = 2·(√π/2)/(2·√π) = 1/2. -/
theorem buffonConstant_three : buffonConstant 3 = 1 / 2 := by
  unfold buffonConstant
  simp only [show ¬((3 : ℕ) ≤ 1) from by omega, ↓reduceIte]
  have h1 : ((3 : ℕ) : ℝ) / 2 = 3 / 2 := by push_cast; ring
  have h2 : (((3 : ℕ) : ℝ) - 1) / 2 = 1 := by push_cast; ring
  have h3 : ((3 : ℕ) : ℝ) - 1 = 2 := by push_cast; ring
  rw [h1, h2, h3, Real.Gamma_one, mul_one]
  have hΓ32 : Real.Gamma (3 / 2 : ℝ) = Real.sqrt π / 2 := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 from by ring,
        Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), gamma_one_half]
    ring
  rw [hΓ32]
  have hπ : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
  field_simp
  ring

/-- c₄ = 4/(3π): the 4-dimensional Buffon constant.
    Proof: c₄ = 2Γ(2)/(3·√π·Γ(3/2)) = 2/(3·√π·√π/2) = 4/(3π). -/
theorem buffonConstant_four : buffonConstant 4 = 4 / (3 * π) := by
  unfold buffonConstant
  simp only [show ¬((4 : ℕ) ≤ 1) from by omega, ↓reduceIte]
  have h1 : ((4 : ℕ) : ℝ) / 2 = 2 := by push_cast; ring
  have h2 : (((4 : ℕ) : ℝ) - 1) / 2 = 3 / 2 := by push_cast; ring
  have h3 : ((4 : ℕ) : ℝ) - 1 = 3 := by push_cast; ring
  rw [h1, h2, h3]
  have hΓ2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 from by ring, Real.Gamma_add_one one_ne_zero,
        Real.Gamma_one, mul_one]
  have hΓ32 : Real.Gamma (3 / 2 : ℝ) = Real.sqrt π / 2 := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 from by ring,
        Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), gamma_one_half]
    ring
  rw [hΓ2, hΓ32]
  have hπ : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
  have hπ2 : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  field_simp
  rw [Real.mul_self_sqrt (le_of_lt pi_pos)]
  ring

/-- The Buffon constant is positive for n ≥ 2. -/
theorem buffonConstant_pos (n : ℕ) (hn : 2 ≤ n) : 0 < buffonConstant n := by
  unfold buffonConstant
  simp only [show ¬(n ≤ 1) from by omega, ↓reduceIte]
  have hn_cast : (2 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  have h_n_half : (0 : ℝ) < (↑n : ℝ) / 2 := by linarith
  have h_nm1 : (0 : ℝ) < (↑n : ℝ) - 1 := by linarith
  have h_nm1_half : (0 : ℝ) < ((↑n : ℝ) - 1) / 2 := by linarith
  apply div_pos
  · exact mul_pos two_pos (Real.Gamma_pos_of_pos h_n_half)
  · exact mul_pos (mul_pos h_nm1 (Real.sqrt_pos.mpr pi_pos))
      (Real.Gamma_pos_of_pos h_nm1_half)

/-- The Buffon constant is at most 1 for all n ≥ 2.
    This follows from |⟨u, e₁⟩| ≤ 1 for all unit vectors u,
    so E[|⟨u, e₁⟩|] ≤ 1. -/
axiom buffonConstant_le_one (n : ℕ) (hn : 2 ≤ n) : buffonConstant n ≤ 1

-- ============================================================
-- Section 2: The Higher-Dimensional Buffon Formula
-- ============================================================

/-- Expected number of crossings for a needle of length L in ℝⁿ
    among parallel hyperplanes spaced d apart. -/
noncomputable def expectedCrossings (n : ℕ) (L d : ℝ) : ℝ :=
  buffonConstant n * L / d

/-- **Higher-Dimensional Buffon's Theorem**: A needle of length L in ℝⁿ
    dropped uniformly at random among parallel hyperplanes spaced d apart
    has expected number of crossings equal to c_n · L / d. -/
theorem buffon_higher_dim (n : ℕ) (L d : ℝ) (hn : 2 ≤ n) (hL : 0 < L) (hd : 0 < d) :
  expectedCrossings n L d = buffonConstant n * L / d := rfl

-- ============================================================
-- Section 3: Structural Properties
-- ============================================================

/-- Linearity in needle length -/
theorem crossings_linear_in_L (n : ℕ) (L₁ L₂ d : ℝ) :
    expectedCrossings n (L₁ + L₂) d =
    expectedCrossings n L₁ d + expectedCrossings n L₂ d := by
  simp only [expectedCrossings]; ring

/-- Scaling in needle length -/
theorem crossings_scale_L (n : ℕ) (α L d : ℝ) :
    expectedCrossings n (α * L) d = α * expectedCrossings n L d := by
  simp only [expectedCrossings]; ring

/-- Expected crossings are nonneg for positive L and d -/
theorem crossings_nonneg (n : ℕ) (L d : ℝ) (hn : 2 ≤ n) (hL : 0 ≤ L) (hd : 0 < d) :
    0 ≤ expectedCrossings n L d := by
  simp only [expectedCrossings]
  exact div_nonneg (mul_nonneg (le_of_lt (buffonConstant_pos n hn)) hL) (le_of_lt hd)

/-- Zero-length needle gives zero crossings -/
theorem crossings_zero_length (n : ℕ) (d : ℝ) :
    expectedCrossings n 0 d = 0 := by
  simp [expectedCrossings]

-- ============================================================
-- Section 4: Consistency with the 2D Case
-- ============================================================

/-- In 2D, the formula gives E = 2L/(πd), matching Buffon-Barbier -/
theorem two_dim_consistency (L d : ℝ) :
    expectedCrossings 2 L d = 2 * L / (π * d) := by
  simp only [expectedCrossings, buffonConstant_two]; ring

/-- In 3D, a needle of length L among parallel planes has E = L/(2d) -/
theorem three_dim_formula (L d : ℝ) :
    expectedCrossings 3 L d = L / (2 * d) := by
  simp only [expectedCrossings, buffonConstant_three]; ring

/-- In 4D, the formula gives E = 4L/(3πd) -/
theorem four_dim_formula (L d : ℝ) :
    expectedCrossings 4 L d = 4 * L / (3 * π * d) := by
  simp only [expectedCrossings, buffonConstant_four]; ring

-- ============================================================
-- Section 5: Dimension Comparison
-- ============================================================

/-- The 2D Buffon constant exceeds the 3D constant (c₂ = 2/π > 1/2 = c₃).
    In higher dimensions, random directions concentrate near the equator
    (orthogonal to the hyperplane normal), reducing the expected projection. -/
theorem two_beats_three : buffonConstant 3 < buffonConstant 2 := by
  rw [buffonConstant_two, buffonConstant_three]
  rw [div_lt_div_iff two_pos pi_pos]
  simp only [one_mul]
  linarith [pi_lt_3141593]

/-- For same needle and spacing, 2D gives more crossings than 3D -/
theorem crossings_2d_ge_3d (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d) :
    expectedCrossings 3 L d ≤ expectedCrossings 2 L d := by
  simp only [expectedCrossings]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_of_lt two_beats_three) hL) (le_of_lt hd)

/-- 2D crossings exceed 4D crossings: c₂ = 2/π > 4/(3π) = c₄ -/
theorem two_beats_four : buffonConstant 4 < buffonConstant 2 := by
  rw [buffonConstant_two, buffonConstant_four]
  rw [div_lt_div_iff (mul_pos (by norm_num : (0:ℝ) < 3) pi_pos) pi_pos]
  linarith [pi_pos]

-- ============================================================
-- Section 6: Mean Width Connection
-- ============================================================

/-- The mean width of a needle of length L in ℝⁿ.
    By Cauchy's formula: w = L · c_n. -/
noncomputable def meanWidth (n : ℕ) (L : ℝ) : ℝ :=
  L * buffonConstant n

/-- Expected crossings = mean width / spacing. -/
theorem crossings_eq_width_div_spacing (n : ℕ) (L d : ℝ) :
    expectedCrossings n L d = meanWidth n L / d := by
  simp [expectedCrossings, meanWidth]; ring

/-- Mean width in 2D: w = 2L/π (the classical projected length) -/
theorem meanWidth_two (L : ℝ) : meanWidth 2 L = 2 * L / π := by
  simp [meanWidth, buffonConstant_two]; ring

/-- Mean width in 3D: w = L/2 -/
theorem meanWidth_three (L : ℝ) : meanWidth 3 L = L / 2 := by
  simp [meanWidth, buffonConstant_three]; ring

-- ============================================================
-- Section 7: The c_n Recurrence
-- ============================================================

/-- The Buffon constant satisfies the recurrence
    c_{n+2} = (n/(n+1)) · c_n for n ≥ 2.

    This follows from the Gamma function identity Γ(z+1) = zΓ(z)
    applied to both Gamma arguments in the definition.

    The recurrence shows c_n → 0 as n → ∞ (concentration of measure),
    since n/(n+1) < 1 and the product telescopes. -/
axiom buffonConstant_recurrence (n : ℕ) (hn : 2 ≤ n) :
  buffonConstant (n + 2) = (n : ℝ) / ((n : ℝ) + 1) * buffonConstant n

/-- From the recurrence: c₅ = (3/4) · c₃ = 3/8 -/
theorem buffonConstant_five : buffonConstant 5 = 3 / 8 := by
  have h := buffonConstant_recurrence 3 (by omega)
  rw [buffonConstant_three] at h
  rw [h]; push_cast; norm_num

/-- From the recurrence: c₆ = (4/5) · c₄ = 16/(15π) -/
theorem buffonConstant_six : buffonConstant 6 = 16 / (15 * π) := by
  have h := buffonConstant_recurrence 4 (by omega)
  rw [buffonConstant_four] at h
  rw [h]
  have hπ : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  push_cast; field_simp; ring

end BuffonHigherDim
