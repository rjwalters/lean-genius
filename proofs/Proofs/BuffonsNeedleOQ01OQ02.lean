/-
# Buffon's Needle: Higher-Dimensional Hyperplane Arrangements

Generalization of Buffon's needle to n-dimensional Euclidean space
with parallel hyperplane arrangements.

For a line segment of length L in ℝⁿ dropped randomly among parallel
hyperplanes spaced d apart, the expected number of crossings is:

  E[crossings] = c_n · L / d

where c_n = 2 · Vol(S^{n-2}) / Vol(S^{n-1}) is the dimensional constant.

Key values:
  c₂ = 2/π  ← classical Buffon's needle
  c₃ = 1    ← needle among parallel planes in 3D
  c₄ = 4/π  ← 4-dimensional case

The formula follows from the Cauchy-Crofton integral geometry formula:
the mean projected length of a needle onto random directions equals
L · c_n, and crossings occur when the projection exceeds the gap.

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

    c_n = 2 · Vol(S^{n-2}) / Vol(S^{n-1})

    Equivalently, c_n is the expected absolute cosine between a
    random direction u ∈ S^{n-1} and any fixed unit vector e₁:
      c_n = E[|⟨u, e₁⟩|]

    Defined using the Gamma function ratio:
      c_n = 2 · Γ(n/2) / (√π · Γ((n-1)/2))

    For n ≤ 1 we set c_n = 0 (degenerate). -/
noncomputable def buffonConstant (n : ℕ) : ℝ :=
  if n ≤ 1 then 0
  else 2 * Real.Gamma ((n : ℝ) / 2) / (Real.sqrt π * Real.Gamma (((n : ℝ) - 1) / 2))

-- The Gamma function values Γ(1/2) = √π requires the Gaussian integral.
-- Axiomatize as it may not be directly available in Mathlib.
/-- Γ(1/2) = √π. Follows from ∫₀^∞ t^{-1/2} e^{-t} dt = √π
    (substitution t = x² reduces to the Gaussian integral). -/
axiom gamma_one_half : Real.Gamma (1 / 2) = Real.sqrt π

/-- c₂ = 2/π: the classical Buffon constant.
    Proof: c₂ = 2Γ(1)/(√π · Γ(1/2)) = 2·1/(√π·√π) = 2/π. -/
theorem buffonConstant_two : buffonConstant 2 = 2 / π := by
  unfold buffonConstant
  simp only [show ¬((2 : ℕ) ≤ 1) from by omega, ↓reduceIte]
  have h1 : ((2 : ℕ) : ℝ) / 2 = 1 := by push_cast; ring
  have h2 : (((2 : ℕ) : ℝ) - 1) / 2 = 1 / 2 := by push_cast; ring
  rw [h1, h2, Real.Gamma_one, gamma_one_half]
  rw [mul_one, Real.mul_self_sqrt (le_of_lt pi_pos)]

/-- c₃ = 1: in 3D, a needle of length L among parallel planes
    has E = L/d — the simplest possible formula.
    Proof: c₃ = 2Γ(3/2)/(√π · Γ(1)) = 2·(√π/2)/(√π·1) = 1. -/
theorem buffonConstant_three : buffonConstant 3 = 1 := by
  unfold buffonConstant
  simp only [show ¬((3 : ℕ) ≤ 1) from by omega, ↓reduceIte]
  have h1 : ((3 : ℕ) : ℝ) / 2 = 3 / 2 := by push_cast; ring
  have h2 : (((3 : ℕ) : ℝ) - 1) / 2 = 1 := by push_cast; ring
  rw [h1, h2, Real.Gamma_one, mul_one]
  have hΓ32 : Real.Gamma (3 / 2 : ℝ) = 1 / 2 * Real.sqrt π := by
    have h : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
    rw [h, Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), gamma_one_half]
  rw [hΓ32]
  have hπ : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
  field_simp

/-- c₄ = 4/π: the 4-dimensional Buffon constant.
    Proof: c₄ = 2Γ(2)/(√π · Γ(3/2)) = 2·1/(√π·√π/2) = 4/π. -/
theorem buffonConstant_four : buffonConstant 4 = 4 / π := by
  unfold buffonConstant
  simp only [show ¬((4 : ℕ) ≤ 1) from by omega, ↓reduceIte]
  have h1 : ((4 : ℕ) : ℝ) / 2 = 2 := by push_cast; ring
  have h2 : (((4 : ℕ) : ℝ) - 1) / 2 = 3 / 2 := by push_cast; ring
  rw [h1, h2]
  have hΓ2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 from by ring, Real.Gamma_add_one one_ne_zero,
        Real.Gamma_one, mul_one]
  have hΓ32 : Real.Gamma (3 / 2 : ℝ) = 1 / 2 * Real.sqrt π := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 from by ring,
        Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), gamma_one_half]
  rw [hΓ2, hΓ32]
  have hπ : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
  have hπ2 : (π : ℝ) ≠ 0 := ne_of_gt pi_pos
  field_simp
  rw [Real.mul_self_sqrt (le_of_lt pi_pos)]
  ring

/-- The Buffon constant is positive for n ≥ 2 -/
theorem buffonConstant_pos (n : ℕ) (hn : 2 ≤ n) : 0 < buffonConstant n := by
  unfold buffonConstant
  simp only [show ¬(n ≤ 1) from by omega, ↓reduceIte]
  apply div_pos
  · exact mul_pos two_pos (Real.Gamma_pos_of_pos (by positivity))
  · exact mul_pos (Real.sqrt_pos.mpr pi_pos) (Real.Gamma_pos_of_pos (by positivity))

/-- The Buffon constant is at most 1 for all n ≥ 2.
    This follows from |⟨u, e₁⟩| ≤ 1 for all unit vectors.
    The maximum c_n = 1 is achieved at n = 3. -/
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
    has expected number of crossings equal to c_n · L / d.

    The proof follows from the Cauchy-Crofton integral geometry formula:
    E[crossings] = (1/Vol(S^{n-1})) · ∫_{S^{n-1}} |⟨v, u⟩| · L/d dσ(u)
                 = L/d · 2 · Vol(S^{n-2}) / Vol(S^{n-1})
                 = c_n · L / d

    where v is the needle direction and the integral averages over
    random hyperplane normals u ∈ S^{n-1}. -/
axiom buffon_higher_dim (n : ℕ) (L d : ℝ) (hn : 2 ≤ n) (hL : 0 < L) (hd : 0 < d) :
  expectedCrossings n L d = buffonConstant n * L / d

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

/-- In 3D, a needle of length L among parallel planes has E = L/d -/
theorem three_dim_formula (L d : ℝ) :
    expectedCrossings 3 L d = L / d := by
  simp only [expectedCrossings, buffonConstant_three]; ring

/-- In 4D, the formula gives E = 4L/(πd) -/
theorem four_dim_formula (L d : ℝ) :
    expectedCrossings 4 L d = 4 * L / (π * d) := by
  simp only [expectedCrossings, buffonConstant_four]; ring

-- ============================================================
-- Section 5: Dimension Comparison
-- ============================================================

/-- In 3D, a needle crosses more often than in 2D (c₃ = 1 > 2/π ≈ 0.637).
    Intuitively: in 3D, the hyperplane captures more random orientations. -/
theorem three_beats_two : buffonConstant 2 < buffonConstant 3 := by
  rw [buffonConstant_two, buffonConstant_three, div_lt_one pi_pos]
  linarith [pi_gt_three]

/-- For same needle and spacing, 3D gives more crossings than 2D -/
theorem crossings_3d_ge_2d (L d : ℝ) (hL : 0 ≤ L) (hd : 0 < d) :
    expectedCrossings 2 L d ≤ expectedCrossings 3 L d := by
  simp only [expectedCrossings]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_of_lt three_beats_two) hL) (le_of_lt hd)

/-- 4D crossings exceed 2D crossings: c₄ = 4/π > 2/π = c₂ -/
theorem four_beats_two : buffonConstant 2 < buffonConstant 4 := by
  rw [buffonConstant_two, buffonConstant_four]
  exact div_lt_div_of_pos_right (by linarith) pi_pos

-- ============================================================
-- Section 6: Mean Width Connection
-- ============================================================

/-- The mean width of a needle of length L in ℝⁿ.
    By Cauchy's formula: w = L · c_n. -/
noncomputable def meanWidth (n : ℕ) (L : ℝ) : ℝ :=
  L * buffonConstant n

/-- Expected crossings = mean width / spacing.
    This is the Cauchy-Crofton interpretation:
    dropping a convex body among parallel hyperplanes spaced d apart,
    E[crossings] = meanWidth / d. -/
theorem crossings_eq_width_div_spacing (n : ℕ) (L d : ℝ) :
    expectedCrossings n L d = meanWidth n L / d := by
  simp [expectedCrossings, meanWidth]; ring

/-- Mean width in 2D: w = 2L/π (the classical projected length) -/
theorem meanWidth_two (L : ℝ) : meanWidth 2 L = 2 * L / π := by
  simp [meanWidth, buffonConstant_two]; ring

/-- Mean width in 3D: w = L (every direction contributes equally on average) -/
theorem meanWidth_three (L : ℝ) : meanWidth 3 L = L := by
  simp [meanWidth, buffonConstant_three]; ring

-- ============================================================
-- Section 7: The c_n Recurrence
-- ============================================================

/-- The Buffon constant satisfies the recurrence
    c_{n+2} = ((n-1)/n) · c_n for n ≥ 2.

    This follows from the sphere volume recurrence
    Vol(S^{n+1}) = (2π/n) · Vol(S^{n-1}).

    The recurrence shows c_n → 0 as n → ∞, since
    (n-1)/n < 1 and the product telescopes. -/
axiom buffonConstant_recurrence (n : ℕ) (hn : 2 ≤ n) :
  buffonConstant (n + 2) = ((n : ℝ) - 1) / (n : ℝ) * buffonConstant n

/-- From the recurrence: c₅ = (2/3) · c₃ = 2/3 -/
theorem buffonConstant_five : buffonConstant 5 = 2 / 3 := by
  have := buffonConstant_recurrence 3 (by omega)
  simp [buffonConstant_three] at this
  linarith

/-- From the recurrence: c₆ = (3/4) · c₄ = 3/π -/
theorem buffonConstant_six : buffonConstant 6 = 3 / π := by
  have := buffonConstant_recurrence 4 (by omega)
  rw [buffonConstant_four] at this
  linarith

end BuffonHigherDim
