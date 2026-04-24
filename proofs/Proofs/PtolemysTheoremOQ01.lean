import Proofs.PtolemysComplexProof
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic

/-!
# Ptolemy Inequality with Concyclicity Characterization (OQ-01)

## What This Proves

This file formalizes the connection between Ptolemy's equality and concyclicity for complex
numbers. Building on `PtolemysComplexProof.lean` (which proves the inequality and the
proportionality characterization), we establish:

1. **Cross-ratio reality**: For z₁,z₂,z₃,z₄ on the unit circle, the Ptolemy ratio
   R = (z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄)) is always real (proved algebraically).

2. **Positivity for CCW order**: For four unit-circle points in counterclockwise order,
   R > 0 (the ratio is a positive real). [sorry: requires inscribed angle theorem]

3. **Ptolemy equality for concyclic CCW points**: Combining the above with
   `ptolemy_equality_of_proportional`, four unit-circle points in CCW order satisfy
   Ptolemy's equality. [conditional on the positivity lemma]

## Key Insight: Conjugation Symmetry

For points on the unit circle, `star z = z⁻¹`. This gives:

  conj(R) = (z₂⁻¹-z₃⁻¹)(z₁⁻¹-z₄⁻¹) / ((z₁⁻¹-z₂⁻¹)(z₃⁻¹-z₄⁻¹))
           = (z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄))   [after field_simp + ring]
           = R

Hence R is real.

## Status
Complete — 0 sorries, 0 axioms.

- `unit_star_eq_inv`: proved via Complex.mul_conj normalization
- `unit_circle_ptolemy_ratio_real`: proved (algebraic conjugation symmetry)
- `ptolemy_ratio_pos_of_ccw`: proved via exp factorization + product-to-sum trig
- `ptolemy_equality_for_unit_circle_ccw`: proved (follows from above)

## Mathlib Dependencies
- `Complex.mul_conj` : `z * conj z = normSq z`
- `starRingEnd ℂ` : complex conjugation as ring endomorphism
- `map_div₀, map_mul, map_sub` : ring homomorphism distributes
- `Complex.exp_re, Complex.exp_im` : real/imaginary parts of exp
- `Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub` : trig addition formulas
- `Real.sin_pos_of_pos_of_lt_pi` : sign of sin on (0, π)
- `ptolemy_equality_of_proportional` (from PtolemysComplexProof)
-/

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: Unit Circle — Conjugate Equals Inverse
-- ============================================================

/-- For a point on the unit circle (‖z‖ = 1), complex conjugation equals inversion.

**Proof**: For ‖z‖ = 1, we have `Complex.normSq z = 1`. The identity
`z * starRingEnd ℂ z = ↑(Complex.normSq z) = 1` (using `Complex.mul_conj`)
gives `starRingEnd ℂ z = z⁻¹` by canceling z.

**Mathlib path**: `Complex.mul_conj z : z * star z = ↑(Complex.normSq z)`, combined with
`Complex.normSq_eq_abs`, `Complex.norm_eq_abs`, and `hz : ‖z‖ = 1`. -/
private lemma unit_star_eq_inv (z : ℂ) (hz : ‖z‖ = 1) : starRingEnd ℂ z = z⁻¹ := by
  have hne : z ≠ 0 := by intro h; simp [h] at hz
  -- z * starRingEnd ℂ z = normSq z = 1
  have hmul : z * starRingEnd ℂ z = 1 := by
    have h1 : z * starRingEnd ℂ z = (Complex.normSq z : ℂ) := Complex.mul_conj z
    rw [h1]
    have hnSq : Complex.normSq z = 1 := by
      have habs : Complex.abs z = 1 := by rwa [← Complex.norm_eq_abs]
      have := Complex.sq_abs z  -- Complex.abs z ^ 2 = Complex.normSq z
      rw [habs, one_pow] at this
      exact this.symm
    exact_mod_cast hnSq
  exact mul_left_cancel₀ hne (hmul.trans (mul_inv_cancel₀ hne).symm)

-- ============================================================
-- PART 2: The Ptolemy Ratio is Real for Unit Circle Points
-- ============================================================

/-- **Cross-Ratio Reality**: For four points on the unit circle, the Ptolemy ratio
R = (z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄)) is invariant under complex conjugation,
hence real.

**Proof**: Substitute `star zᵢ = zᵢ⁻¹` (unit circle), then `field_simp + ring`
verifies the algebraic identity. The key computation:
  conj R = (z₂⁻¹-z₃⁻¹)(z₁⁻¹-z₄⁻¹) / ((z₁⁻¹-z₂⁻¹)(z₃⁻¹-z₄⁻¹))
After clearing denominators (multiplying by z₁z₂z₃z₄), both conj R and R have the same
cleared-denominator form: (z₃-z₂)(z₄-z₁)·(z₁-z₂)·(z₃-z₄) = (z₂-z₃)(z₁-z₄)·(z₁-z₂)·(z₃-z₄).
-/
theorem unit_circle_ptolemy_ratio_real (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0) :
    starRingEnd ℂ ((z₂ - z₃) * (z₁ - z₄) / ((z₁ - z₂) * (z₃ - z₄))) =
    (z₂ - z₃) * (z₁ - z₄) / ((z₁ - z₂) * (z₃ - z₄)) := by
  have ne1 : z₁ ≠ 0 := by intro h; simp [h] at h₁
  have ne2 : z₂ ≠ 0 := by intro h; simp [h] at h₂
  have ne3 : z₃ ≠ 0 := by intro h; simp [h] at h₃
  have ne4 : z₄ ≠ 0 := by intro h; simp [h] at h₄
  have ne12 : z₁ - z₂ ≠ 0 := left_ne_zero_of_mul hdenom
  have ne34 : z₃ - z₄ ≠ 0 := right_ne_zero_of_mul hdenom
  -- Expand conjugation over div/mul/sub, substitute star zᵢ = zᵢ⁻¹
  simp only [map_div₀, map_mul, map_sub,
             unit_star_eq_inv z₁ h₁, unit_star_eq_inv z₂ h₂,
             unit_star_eq_inv z₃ h₃, unit_star_eq_inv z₄ h₄]
  -- Both sides are equal: clear denominators via field_simp, close with ring
  have inv_ne12 : z₁⁻¹ - z₂⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    exact fun heq => ne12 (sub_eq_zero.mpr
      (by have := congr_arg Inv.inv heq; simp only [inv_inv] at this; exact this))
  have inv_ne34 : z₃⁻¹ - z₄⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    exact fun heq => ne34 (sub_eq_zero.mpr
      (by have := congr_arg Inv.inv heq; simp only [inv_inv] at this; exact this))
  rw [div_eq_div_iff (mul_ne_zero inv_ne12 inv_ne34) hdenom]
  field_simp [ne1, ne2, ne3, ne4]
  ring

/-- The ratio is real: extract as a real number. -/
theorem unit_circle_ptolemy_ratio_is_real (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0) :
    ∃ t : ℝ, (t : ℂ) = (z₂ - z₃) * (z₁ - z₄) / ((z₁ - z₂) * (z₃ - z₄)) := by
  set R := (z₂ - z₃) * (z₁ - z₄) / ((z₁ - z₂) * (z₃ - z₄)) with hR_def
  have hconj : starRingEnd ℂ R = R :=
    unit_circle_ptolemy_ratio_real z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hdenom
  -- From conj R = R, we get R.im = 0, so R = ↑R.re
  have him : R.im = 0 := by
    have := congr_arg Complex.im hconj
    simp [Complex.conj_im] at this
    linarith
  exact ⟨R.re, Complex.ext (by simp) (by simp [him])⟩

-- ============================================================
-- PART 3: Positivity for Counterclockwise Ordering
-- ============================================================

-- Helper: real and imaginary parts of exp(iθ) for θ : ℝ
private lemma exp_mul_I_re (θ : ℝ) :
    (Complex.exp (↑θ * Complex.I)).re = Real.cos θ := by
  simp [Complex.exp_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Real.exp_zero]

private lemma exp_mul_I_im (θ : ℝ) :
    (Complex.exp (↑θ * Complex.I)).im = Real.sin θ := by
  simp [Complex.exp_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Real.exp_zero]

/-- Factorization: exp(iα) - exp(iβ) = 2·I·sin((α-β)/2)·exp(i(α+β)/2)

Proof: using sum-to-product identities for cos and sin:
  cos α - cos β = -2·sin((α-β)/2)·sin((α+β)/2)
  sin α - sin β =  2·sin((α-β)/2)·cos((α+β)/2) -/
private lemma exp_diff_factor (α β : ℝ) :
    Complex.exp (↑α * Complex.I) - Complex.exp (↑β * Complex.I) =
    2 * Complex.I * ↑(Real.sin ((α - β) / 2)) *
    Complex.exp (↑((α + β) / 2) * Complex.I) := by
  apply Complex.ext
  · -- Real part: cos α - cos β = Re(2I·s·exp(im)) = -2·s·sin(m)
    --   where s = sin((α-β)/2), m = (α+β)/2
    rw [Complex.sub_re, exp_mul_I_re, exp_mul_I_re]
    -- Compute Re of RHS
    have hrhs : (2 * Complex.I * ↑(Real.sin ((α - β) / 2)) *
        Complex.exp (↑((α + β) / 2) * Complex.I)).re =
        -2 * Real.sin ((α - β) / 2) * Real.sin ((α + β) / 2) := by
      have h1 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).re = 0 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
        ring
      have h2 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).im =
          2 * Real.sin ((α - β) / 2) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
        ring
      rw [Complex.mul_re, h1, h2, exp_mul_I_re, exp_mul_I_im]; ring
    rw [hrhs]
    -- cos α - cos β = -2·sin((α-β)/2)·sin((α+β)/2)  [product-to-sum]
    have hca : Real.cos α = Real.cos ((α + β) / 2 + (α - β) / 2) := by congr 1; ring
    have hcb : Real.cos β = Real.cos ((α + β) / 2 - (α - β) / 2) := by congr 1; ring
    rw [hca, hcb, Real.cos_add, Real.cos_sub]; ring
  · -- Imaginary part: sin α - sin β = Im(2I·s·exp(im)) = 2·s·cos(m)
    rw [Complex.sub_im, exp_mul_I_im, exp_mul_I_im]
    have hrhs : (2 * Complex.I * ↑(Real.sin ((α - β) / 2)) *
        Complex.exp (↑((α + β) / 2) * Complex.I)).im =
        2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) := by
      have h1 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).re = 0 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
        ring
      have h2 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).im =
          2 * Real.sin ((α - β) / 2) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im]
        ring
      rw [Complex.mul_im, h1, h2, exp_mul_I_re, exp_mul_I_im]; ring
    rw [hrhs]
    -- sin α - sin β = 2·sin((α-β)/2)·cos((α+β)/2)  [product-to-sum]
    have hsa : Real.sin α = Real.sin ((α + β) / 2 + (α - β) / 2) := by congr 1; ring
    have hsb : Real.sin β = Real.sin ((α + β) / 2 - (α - β) / 2) := by congr 1; ring
    rw [hsa, hsb, Real.sin_add, Real.sin_sub]; ring

-- Helper: sin is negative on (-π, 0)
private lemma sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx : x < 0) (hx' : -Real.pi < x) :
    Real.sin x < 0 := by
  have hpos : 0 < -x := by linarith
  have hlt : -x < Real.pi := by linarith
  have hpos_sin := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  rwa [Real.sin_neg, neg_pos] at hpos_sin

/-- Four unit-circle points in counterclockwise order.
    Encoded as angles: θ₁ < θ₂ < θ₃ < θ₄ < θ₁ + 2π with zᵢ = exp(i·θᵢ). -/
def IsCCWOrder (z₁ z₂ z₃ z₄ : ℂ) : Prop :=
  ∃ θ₁ θ₂ θ₃ θ₄ : ℝ,
    θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < θ₁ + 2 * Real.pi ∧
    z₁ = Complex.exp (↑θ₁ * Complex.I) ∧
    z₂ = Complex.exp (↑θ₂ * Complex.I) ∧
    z₃ = Complex.exp (↑θ₃ * Complex.I) ∧
    z₄ = Complex.exp (↑θ₄ * Complex.I)

/-- **Positivity Theorem** (proved via trig factorization):

For four unit-circle points in CCW order, ∃ t > 0 with (z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄).

**Proof sketch** (via trig expansion):
Writing zⱼ = exp(iθⱼ), the identity `e^(iα) - e^(iβ) = 2i·sin((α-β)/2)·e^(i(α+β)/2)` gives:
  z₂-z₃ = 2i·sin((θ₂-θ₃)/2)·exp(i(θ₂+θ₃)/2)
  z₁-z₄ = 2i·sin((θ₁-θ₄)/2)·exp(i(θ₁+θ₄)/2)
  z₁-z₂ = 2i·sin((θ₁-θ₂)/2)·exp(i(θ₁+θ₂)/2)
  z₃-z₄ = 2i·sin((θ₃-θ₄)/2)·exp(i(θ₃+θ₄)/2)

The ratio: R = [sin((θ₂-θ₃)/2)·sin((θ₁-θ₄)/2)] / [sin((θ₁-θ₂)/2)·sin((θ₃-θ₄)/2)]
(phase factors cancel: θ₁+θ₂+θ₃+θ₄ in num and denom; (2i)² cancels similarly)

For CCW order θ₁<θ₂<θ₃<θ₄<θ₁+2π: all four sine arguments are in (-π,0), so all four
sine values are negative → R = (-)(-)/((-)(-)) > 0.

**Proof**: Factor each difference using `exp_diff_factor`. The exponential phase factors
all combine to exp(i(θ₁+θ₂+θ₃+θ₄)/2) and cancel. The (2i)² = -4 factors cancel.
The ratio of sine products is positive since all four arguments lie in (-π, 0). -/
lemma ptolemy_ratio_pos_of_ccw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0)
    (hnumer : (z₂ - z₃) * (z₁ - z₄) ≠ 0)
    (hccw : IsCCWOrder z₁ z₂ z₃ z₄) :
    ∃ t : ℝ, 0 < t ∧
      (z₂ - z₃) * (z₁ - z₄) = (t : ℂ) * ((z₁ - z₂) * (z₃ - z₄)) := by
  obtain ⟨θ₁, θ₂, θ₃, θ₄, h12, h23, h34, h41, rfl, rfl, rfl, rfl⟩ := hccw
  -- Half-angle sine values
  set s₂₃ := Real.sin ((θ₂ - θ₃) / 2) with hs₂₃_def
  set s₁₄ := Real.sin ((θ₁ - θ₄) / 2) with hs₁₄_def
  set s₁₂ := Real.sin ((θ₁ - θ₂) / 2) with hs₁₂_def
  set s₃₄ := Real.sin ((θ₃ - θ₄) / 2) with hs₃₄_def
  -- All four arguments lie in (-π, 0), so all four sines are negative
  -- Bound: θⱼ - θₖ > -2π (from θₖ < θ₁ + 2π ≤ θⱼ + 2π for all j,k)
  have hs₂₃_neg : s₂₃ < 0 := by
    apply sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · have : θ₃ - θ₂ < 2 * Real.pi := by linarith
      linarith
  have hs₁₄_neg : s₁₄ < 0 := by
    apply sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · linarith
  have hs₁₂_neg : s₁₂ < 0 := by
    apply sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · have : θ₂ - θ₁ < 2 * Real.pi := by linarith
      linarith
  have hs₃₄_neg : s₃₄ < 0 := by
    apply sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · have : θ₄ - θ₃ < 2 * Real.pi := by linarith
      linarith
  -- Numerator and denominator of t are positive
  have hnum_pos : 0 < s₂₃ * s₁₄ := mul_pos_of_neg_of_neg hs₂₃_neg hs₁₄_neg
  have hden_pos : 0 < s₁₂ * s₃₄ := mul_pos_of_neg_of_neg hs₁₂_neg hs₃₄_neg
  have hden_ne : s₁₂ * s₃₄ ≠ 0 := ne_of_gt hden_pos
  -- t = s₂₃·s₁₄ / (s₁₂·s₃₄) > 0
  refine ⟨s₂₃ * s₁₄ / (s₁₂ * s₃₄), div_pos hnum_pos hden_pos, ?_⟩
  -- Factor each complex difference using exp_diff_factor:
  --   zⱼ - zₖ = 2I·sin((θⱼ-θₖ)/2)·exp(i(θⱼ+θₖ)/2)
  have hf23 : Complex.exp (↑θ₂ * Complex.I) - Complex.exp (↑θ₃ * Complex.I) =
      2 * Complex.I * ↑s₂₃ * Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) :=
    exp_diff_factor θ₂ θ₃
  have hf14 : Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₄ * Complex.I) =
      2 * Complex.I * ↑s₁₄ * Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I) :=
    exp_diff_factor θ₁ θ₄
  have hf12 : Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₂ * Complex.I) =
      2 * Complex.I * ↑s₁₂ * Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I) :=
    exp_diff_factor θ₁ θ₂
  have hf34 : Complex.exp (↑θ₃ * Complex.I) - Complex.exp (↑θ₄ * Complex.I) =
      2 * Complex.I * ↑s₃₄ * Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I) :=
    exp_diff_factor θ₃ θ₄
  -- The exponential phase factors combine identically on both sides:
  -- E₂₃ · E₁₄ = exp(i(θ₁+θ₂+θ₃+θ₄)/2) = E₁₂ · E₃₄
  have hE : Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) *
            Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I) =
            Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I) *
            Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  -- Substitute factorizations and the phase identity, then close by field arithmetic
  rw [hf23, hf14, hf12, hf34]
  -- Isolate E₂₃ * E₁₄ on the LHS, then apply hE to get E₁₂ * E₃₄
  -- Goal: (2I·s₂₃·E₂₃)·(2I·s₁₄·E₁₄) = ↑(s₂₃·s₁₄/(s₁₂·s₃₄))·((2I·s₁₂·E₁₂)·(2I·s₃₄·E₃₄))
  have lhs_eq : (2 * Complex.I * ↑s₂₃ * Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I)) *
                (2 * Complex.I * ↑s₁₄ * Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I)) =
                -4 * ↑s₂₃ * ↑s₁₄ *
                (Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) *
                 Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I)) := by ring
  rw [lhs_eq, hE]
  push_cast
  have hs₁₂_C : (↑s₁₂ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (neg_pos.mpr hs₁₂_neg)
  have hs₃₄_C : (↑s₃₄ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (neg_pos.mpr hs₃₄_neg)
  field_simp [hs₁₂_C, hs₃₄_C]
  ring

-- ============================================================
-- PART 4: Main Theorem — Ptolemy Equality for Concyclic CCW Points
-- ============================================================

/-- **Ptolemy Equality for Unit-Circle Points in CCW Order**

For four distinct points on the unit circle in counterclockwise order:
  ‖z₁-z₃‖ · ‖z₂-z₄‖ = ‖z₁-z₂‖ · ‖z₃-z₄‖ + ‖z₂-z₃‖ · ‖z₁-z₄‖

**Proof**:
1. By `ptolemy_ratio_pos_of_ccw`: ∃ t > 0 with (z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)
2. By `ptolemy_equality_of_proportional` (t ≥ 0): Ptolemy equality follows. -/
theorem ptolemy_equality_for_unit_circle_ccw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0)
    (hnumer : (z₂ - z₃) * (z₁ - z₄) ≠ 0)
    (hccw : IsCCWOrder z₁ z₂ z₃ z₄) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  obtain ⟨t, ht_pos, ht_eq⟩ :=
    ptolemy_ratio_pos_of_ccw z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hdenom hnumer hccw
  exact ptolemy_equality_of_proportional z₁ z₂ z₃ z₄ t ht_pos.le ht_eq

-- ============================================================
-- PART 5: Concyclicity and General Circles
-- ============================================================

/-- Four complex numbers are concyclic: they lie on a common circle. -/
def IsConcyclic₄ (z₁ z₂ z₃ z₄ : ℂ) : Prop :=
  ∃ (c : ℂ) (r : ℝ), 0 < r ∧
    ‖z₁ - c‖ = r ∧ ‖z₂ - c‖ = r ∧ ‖z₃ - c‖ = r ∧ ‖z₄ - c‖ = r

/-- Normalizing concyclic points to the unit circle: if all ‖zᵢ - c‖ = r, then
    wᵢ := (zᵢ - c) / r satisfies ‖wᵢ‖ = 1. -/
lemma concyclic_normalize_to_unit (z c : ℂ) (r : ℝ) (hr : 0 < r) (h : ‖z - c‖ = r) :
    ‖(z - c) / (r : ℂ)‖ = 1 := by
  rw [map_div₀, Complex.norm_real, Real.norm_of_nonneg hr.le, h, div_self (ne_of_gt hr)]

/-- Ptolemy equality is preserved under translation and positive scaling.
    If z'ᵢ = (zᵢ - c)/r, then Ptolemy equality for z'ᵢ ↔ Ptolemy equality for zᵢ. -/
lemma ptolemy_iff_normalized (z₁ z₂ z₃ z₄ c : ℂ) (r : ℝ) (hr : 0 < r)
    (hr_ne : (r : ℂ) ≠ 0) :
    (‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) ↔
    (‖(z₁-c)/r - (z₃-c)/r‖ * ‖(z₂-c)/r - (z₄-c)/r‖ =
     ‖(z₁-c)/r - (z₂-c)/r‖ * ‖(z₃-c)/r - (z₄-c)/r‖ +
     ‖(z₂-c)/r - (z₃-c)/r‖ * ‖(z₁-c)/r - (z₄-c)/r‖) := by
  -- The normalized differences: (zᵢ-c)/r - (zⱼ-c)/r = (zᵢ-zⱼ)/r
  have simp_diff : ∀ a b : ℂ, (a - c) / r - (b - c) / r = (a - b) / r := by
    intros a b; field_simp; ring
  simp only [simp_diff]
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  constructor
  · intro h
    have hr_pos : 0 < r := hr
    field_simp [ne_of_gt hr_pos]
    linarith [mul_pos hr_pos hr_pos, h]
  · intro h
    have hr_pos : 0 < r := hr
    field_simp [ne_of_gt hr_pos] at h
    linarith [mul_pos hr_pos hr_pos, h]

/-- **Ptolemy Equality for Concyclic Points in CCW Convex Position**

For four distinct concyclic points, after normalizing to the unit circle (by centering
at c and scaling by r), if the normalized points are in CCW order, Ptolemy's equality holds.

**Proof structure**:
1. Normalize: wᵢ = (zᵢ - c) / r has ‖wᵢ‖ = 1 (unit circle)
2. If normalized points are in CCW order: apply `ptolemy_equality_for_unit_circle_ccw`
3. Scale back: Ptolemy equality is invariant under translation/scaling

**Note on CCW condition**: The CCW order must be stated for the normalized points.
For an arbitrary circle with center c and radius r, the ordering of points on the circle
is the same before and after normalization. -/
theorem ptolemy_equality_for_concyclic (z₁ z₂ z₃ z₄ : ℂ)
    (hcyc : IsConcyclic₄ z₁ z₂ z₃ z₄) :
    let c := hcyc.choose
    let r := hcyc.choose_spec.choose
    ∀ (hr : 0 < r)
      (hdenom : ((z₁-c)/r - (z₂-c)/r) * ((z₃-c)/r - (z₄-c)/r) ≠ 0)
      (hnumer : ((z₂-c)/r - (z₃-c)/r) * ((z₁-c)/r - (z₄-c)/r) ≠ 0)
      (hccw : IsCCWOrder ((z₁-c)/r) ((z₂-c)/r) ((z₃-c)/r) ((z₄-c)/r)),
      ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  intro c r hr hdenom hnumer hccw
  obtain ⟨_, hc1, hc2, hc3, hc4⟩ := hcyc.choose_spec.choose_spec
  -- Normalized points are on the unit circle
  have w₁_unit : ‖(z₁ - c) / (r : ℂ)‖ = 1 := concyclic_normalize_to_unit z₁ c r hr hc1
  have w₂_unit : ‖(z₂ - c) / (r : ℂ)‖ = 1 := concyclic_normalize_to_unit z₂ c r hr hc2
  have w₃_unit : ‖(z₃ - c) / (r : ℂ)‖ = 1 := concyclic_normalize_to_unit z₃ c r hr hc3
  have w₄_unit : ‖(z₄ - c) / (r : ℂ)‖ = 1 := concyclic_normalize_to_unit z₄ c r hr hc4
  -- Simplify: (zᵢ-c)/r - (zⱼ-c)/r = (zᵢ-zⱼ)/r
  have simp_diff : ∀ a b : ℂ, (a - c) / r - (b - c) / r = (a - b) / r := by
    intros a b; field_simp; ring
  rw [simp_diff] at hdenom hnumer
  -- Apply unit circle theorem to normalized points
  have ptolemy_norm := ptolemy_equality_for_unit_circle_ccw
    ((z₁-c)/r) ((z₂-c)/r) ((z₃-c)/r) ((z₄-c)/r)
    w₁_unit w₂_unit w₃_unit w₄_unit
    (by rwa [simp_diff, simp_diff])
    (by rwa [simp_diff, simp_diff])
    hccw
  -- Scale back using ptolemy_iff_normalized
  rwa [← ptolemy_iff_normalized z₁ z₂ z₃ z₄ c r hr (by exact_mod_cast ne_of_gt hr)]

-- ============================================================
-- PART 6: Numerical Verification
-- ============================================================

/-- The Ptolemy inequality holds (from PtolemysComplexProof). -/
theorem ptolemy_ineq_summary (z₁ z₂ z₃ z₄ : ℂ) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ ≤ ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ :=
  ptolemy_inequality z₁ z₂ z₃ z₄

/-- Unit square corners {1, i, -1, -i} are concyclic on the unit circle.
    Their Ptolemy ratio R = (-i·(-1)-(-1)·(-i)) / ((1-i)·(-1-(-i)))
    Let's verify the equality: ‖1-(-1)‖·‖i-(-i)‖ = ‖1-i‖·‖(-1)-(-i)‖ + ‖i-(-1)‖·‖1-(-i)‖ -/
example :
    ‖(1 : ℂ) - (-1)‖ * ‖Complex.I - (-Complex.I)‖ =
    ‖(1 : ℂ) - Complex.I‖ * ‖(-1 : ℂ) - (-Complex.I)‖ +
    ‖Complex.I - (-1 : ℂ)‖ * ‖(1 : ℂ) - (-Complex.I)‖ := by
  simp only [Complex.norm_eq_abs, map_add, map_sub, map_neg, map_one,
             Complex.abs_I, Complex.abs_one, Complex.abs_neg]
  norm_num [Complex.abs_apply, Complex.normSq_apply]

/-- For non-concyclic points, Ptolemy inequality is strict.
    Points 0, 1, 2, i are NOT all concyclic (one lies on the x-axis, not on the circle
    through 0, 1, i). The Ptolemy inequality is strict here. -/
example :
    ‖(0 : ℂ) - 2‖ * ‖(1 : ℂ) - Complex.I‖ <
    ‖(0 : ℂ) - 1‖ * ‖(2 : ℂ) - Complex.I‖ +
    ‖(1 : ℂ) - 2‖ * ‖(0 : ℂ) - Complex.I‖ := by
  norm_num [Complex.norm_eq_abs, Complex.abs_apply, Complex.normSq_apply]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
             Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num),
             Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num)]

-- ============================================================
-- PART 7: Summary
-- ============================================================

/-!
## Complete Ptolemy Characterization (informal summary)

For four distinct complex numbers z₁, z₂, z₃, z₄ in convex position, the following
are equivalent:

1. **Ptolemy equality**: ‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖
2. **SameRay**: `SameRay ℝ ((z₁-z₂)(z₃-z₄)) ((z₂-z₃)(z₁-z₄))`
   (from `PtolemysComplexProofOQ01.lean`)
3. **Positive cross-ratio**: R = (z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄)) is a positive real
4. **Concyclicity in CCW order**: z₁, z₂, z₃, z₄ lie on a common circle in CCW order

The present file proves:
- (3 → 2 → 1): If R > 0, Ptolemy equality holds (algebraic)
- (4 → 3): If CCW concyclic, R > 0 [requires `ptolemy_ratio_pos_of_ccw`, currently sorry]
- Unit circle cross-ratio is always real (1 → 3 for unit circle case), proved algebraically
-/

#check @unit_circle_ptolemy_ratio_real
#check @ptolemy_equality_for_unit_circle_ccw
#check @ptolemy_equality_for_concyclic
