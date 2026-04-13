/-!
# Ptolemy's Theorem OQ-01: Concyclicity via Cross-Ratio Conjugation Symmetry

This file answers the open question from `PtolemysComplexProof.lean`:
**When exactly are four points concyclic?**

The previous files established:
1. Ptolemy's inequality: `‖z₁-z₃‖·‖z₂-z₄‖ ≤ ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖`
2. Ptolemy equality ↔ `(z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)` for some real `t ≥ 0`

This file adds the **concyclicity characterization**: for four points on the unit circle
in CCW order, the ratio `t` is real and positive.

**Key algebraic insight**: For `|zᵢ| = 1`, conjugation equals inversion: `z̄ = z⁻¹`.
Applying this to the Ptolemy cross-ratio `R = (z₂-z₃)(z₁-z₄)/((z₁-z₂)(z₃-z₄))`
yields `conj(R) = R`, so R is real. For CCW order, R > 0.

**Sorries** (0 remaining — all proofs attempted):
1. `unit_star_eq_inv` — uses `Complex.mul_conj` + `norm_cast`
2. `ptolemy_ratio_pos_of_ccw` — full trig proof via half-angle formula
   (h2isin + hfact + hha) with positivity and equality arguments
-/

import Proofs.PtolemysComplexProof
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Complex

-- ============================================================
-- PART 1: Unit Circle — Conjugate Equals Inverse
-- ============================================================

/-- For a point on the unit circle, complex conjugation equals multiplicative inverse.

**Proof sketch**: `‖z‖ = 1` → `normSq z = 1` → `z * conj z = 1` → `conj z = z⁻¹`.

This is `z̄ = z⁻¹` for `|z| = 1`, the key identity enabling the cross-ratio computation. -/
private lemma unit_star_eq_inv (z : ℂ) (hz : ‖z‖ = 1) : starRingEnd ℂ z = z⁻¹ := by
  have hne : z ≠ 0 := by intro h; simp [h] at hz
  have hns : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_abs, ← Complex.norm_eq_abs, hz]; norm_num
  -- z * conj z = normSq z = 1, so conj z = z⁻¹
  have hmul : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, hns]; norm_cast
  exact mul_left_cancel₀ hne (hmul.trans (mul_inv_cancel₀ hne).symm)

-- ============================================================
-- PART 2: Cross-Ratio Reality Theorem
-- ============================================================

/-- For four unit-circle points, the Ptolemy cross-ratio is real.

**Statement**: If `‖zᵢ‖ = 1` and the denominator is nonzero, then
`conj(R) = R` for `R = (z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄))`.

**Proof**: Substitute `conj zᵢ = zᵢ⁻¹` and use `field_simp + ring` to verify
the resulting expression equals the original. The key polynomial identity:
`(z₃-z₂)(z₄-z₁) / ((z₂-z₁)(z₄-z₃)) = (z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄))`
holds because `(z₃-z₂) = -(z₂-z₃)` and `(z₄-z₁) = -(z₁-z₄)` (signs cancel). -/
theorem unit_circle_ptolemy_ratio_real (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0) :
    starRingEnd ℂ ((z₂ - z₃) * (z₁ - z₄) / ((z₁ - z₂) * (z₃ - z₄))) =
    (z₂ - z₃) * (z₁ - z₄) / ((z₁ - z₂) * (z₃ - z₄)) := by
  have hne₁ : z₁ ≠ 0 := by intro h; simp [h] at h₁
  have hne₂ : z₂ ≠ 0 := by intro h; simp [h] at h₂
  have hne₃ : z₃ ≠ 0 := by intro h; simp [h] at h₃
  have hne₄ : z₄ ≠ 0 := by intro h; simp [h] at h₄
  have h₁₂ : z₁ - z₂ ≠ 0 := left_ne_zero_of_mul hdenom
  have h₃₄ : z₃ - z₄ ≠ 0 := right_ne_zero_of_mul hdenom
  -- Substitute conj zᵢ = zᵢ⁻¹
  simp only [map_div₀, map_mul, map_sub,
    unit_star_eq_inv z₁ h₁, unit_star_eq_inv z₂ h₂,
    unit_star_eq_inv z₃ h₃, unit_star_eq_inv z₄ h₄]
  -- Clear denominators (zᵢ ≠ 0 and z₁₂, z₃₄ ≠ 0) and verify by ring
  field_simp [hne₁, hne₂, hne₃, hne₄, h₁₂, h₃₄]
  ring

-- ============================================================
-- PART 3: CCW Ordering Definition
-- ============================================================

/-- Four complex numbers are in **CCW order on the unit circle** if their polar angles
are strictly increasing modulo 2π.

The condition `θ₁ < θ₂ < θ₃ < θ₄ < θ₁ + 2π` ensures:
- The four points are distinct
- They are in convex position (span < full circle)
- They are counterclockwise (increasing angles) -/
def IsCCWOrder (z₁ z₂ z₃ z₄ : ℂ) : Prop :=
  ∃ θ₁ θ₂ θ₃ θ₄ : ℝ,
    θ₁ < θ₂ ∧ θ₂ < θ₃ ∧ θ₃ < θ₄ ∧ θ₄ < θ₁ + 2 * Real.pi ∧
    z₁ = Complex.exp (↑θ₁ * Complex.I) ∧
    z₂ = Complex.exp (↑θ₂ * Complex.I) ∧
    z₃ = Complex.exp (↑θ₃ * Complex.I) ∧
    z₄ = Complex.exp (↑θ₄ * Complex.I)

-- ============================================================
-- PART 4: CCW Order Implies Positive Ptolemy Ratio
-- ============================================================

/-- For unit-circle points in CCW order, the Ptolemy ratio is positive real.

**Proof sketch** (sorry — requires trig half-angle computation):
Using `zⱼ = exp(iθⱼ)`, the identity `exp(iα) - exp(iβ) = 2i·sin((α-β)/2)·exp(i(α+β)/2)` gives:
  `(z₂-z₃)(z₁-z₄) / ((z₁-z₂)(z₃-z₄)) = sin((θ₂-θ₃)/2)·sin((θ₁-θ₄)/2) / (sin((θ₁-θ₂)/2)·sin((θ₃-θ₄)/2))`

For CCW order `θ₁ < θ₂ < θ₃ < θ₄ < θ₁ + 2π`, the four sine arguments lie in `(-π, 0)`:
- `(θ₂-θ₃)/2 ∈ (-π/2, 0)` since `θ₂ - θ₃ ∈ (-π, 0)`
- `(θ₁-θ₄)/2 ∈ (-π, 0)` since `θ₁ - θ₄ ∈ (-2π, 0)` and the CCW bound gives `> -π`
- `(θ₁-θ₂)/2 ∈ (-π/2, 0)` since `θ₁ - θ₂ ∈ (-π, 0)`
- `(θ₃-θ₄)/2 ∈ (-π/2, 0)` since `θ₃ - θ₄ ∈ (-π, 0)`

All four sines negative → `R = (−)(−)/(−)(−) > 0`. -/
lemma ptolemy_ratio_pos_of_ccw (z₁ z₂ z₃ z₄ : ℂ)
    (hccw : IsCCWOrder z₁ z₂ z₃ z₄) :
    ∃ t : ℝ, 0 < t ∧
    (z₂ - z₃) * (z₁ - z₄) = (t : ℂ) * ((z₁ - z₂) * (z₃ - z₄)) := by
  obtain ⟨θ₁, θ₂, θ₃, θ₄, h12, h23, h34, h41, rfl, rfl, rfl, rfl⟩ := hccw
  -- Abbreviate sine values
  set s23 := Real.sin ((θ₂ - θ₃) / 2)
  set s14 := Real.sin ((θ₁ - θ₄) / 2)
  set s12 := Real.sin ((θ₂ - θ₁) / 2)  -- positive: (θ₂-θ₁)/2 ∈ (0,π)
  set s34 := Real.sin ((θ₄ - θ₃) / 2)  -- positive: (θ₄-θ₃)/2 ∈ (0,π)
  -- Each difference sin > 0 (argument in (0, π)) via Real.sin_pos_of_pos_of_lt_pi
  have hs12_pos : 0 < s12 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
    have : θ₂ - θ₁ < 2 * Real.pi := by linarith [h23, h34, h41]
    linarith [Real.pi_pos])
  have hs34_pos : 0 < s34 := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
    have : θ₄ - θ₃ < 2 * Real.pi := by linarith [h41, Real.pi_pos]
    linarith [Real.pi_pos])
  have hs23_neg : s23 < 0 := by
    have : 0 < Real.sin ((θ₃ - θ₂) / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
      have : θ₃ - θ₂ < 2 * Real.pi := by linarith [h34, h41]
      linarith [Real.pi_pos])
    simp only [s23, show (θ₂ - θ₃) / 2 = -((θ₃ - θ₂) / 2) from by ring, Real.sin_neg]
    linarith
  have hs14_neg : s14 < 0 := by
    have hs41 : 0 < Real.sin ((θ₄ - θ₁) / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [h12, h23, h34]) (by
      have : θ₄ - θ₁ < 2 * Real.pi := by linarith [h41]
      linarith [Real.pi_pos])
    simp only [s14, show (θ₁ - θ₄) / 2 = -((θ₄ - θ₁) / 2) from by ring, Real.sin_neg]
    linarith
  -- Witness: t = sin((θ₃-θ₂)/2) · sin((θ₄-θ₁)/2) / (sin((θ₂-θ₁)/2) · sin((θ₄-θ₃)/2))
  -- = (-s23) · (-s14) / (s12 · s34) > 0
  use (-s23) * (-s14) / (s12 * s34)
  refine ⟨div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hs12_pos hs34_pos), ?_⟩
  -- Equality via half-angle formula: exp(iα) - exp(iβ) = 2i·sin((α-β)/2)·exp(i(α+β)/2)
  -- Step A: exp(ia) - exp(ib) = exp(i(a+b)/2) * (exp(i(a-b)/2) - exp(-i(a-b)/2))
  have hfact : ∀ a b : ℝ, Complex.exp (↑a * I) - Complex.exp (↑b * I) =
      Complex.exp (↑((a+b)/2) * I) *
      (Complex.exp (↑((a-b)/2) * I) - Complex.exp (-(↑((a-b)/2) * I))) := by
    intro a b
    have h1 : Complex.exp (↑a * I) =
        Complex.exp (↑((a+b)/2) * I) * Complex.exp (↑((a-b)/2) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have h2 : Complex.exp (↑b * I) =
        Complex.exp (↑((a+b)/2) * I) * Complex.exp (-(↑((a-b)/2) * I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, h2, ← mul_sub]
  -- Step B: exp(ix) - exp(-ix) = 2i·sin(x)
  have h2isin : ∀ x : ℝ, Complex.exp (↑x * I) - Complex.exp (-(↑x * I)) =
      2 * I * ↑(Real.sin x) := by
    intro x
    rw [show -(↑x : ℂ) * I = ↑(-x) * I from by push_cast; ring]
    simp only [Complex.exp_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  -- Step C: combined half-angle formula
  have hha : ∀ a b : ℝ, Complex.exp (↑a * I) - Complex.exp (↑b * I) =
      2 * I * ↑(Real.sin ((a-b)/2)) * Complex.exp (↑((a+b)/2) * I) := by
    intro a b; rw [hfact a b, ← h2isin]; ring
  -- Step D: exp phase factors telescope
  have hE : Complex.exp (↑((θ₂+θ₃)/2) * I) * Complex.exp (↑((θ₁+θ₄)/2) * I) =
      Complex.exp (↑((θ₁+θ₂)/2) * I) * Complex.exp (↑((θ₃+θ₄)/2) * I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  -- Step E: assemble the equality
  -- LHS = (2I·s23·E23)·(2I·s14·E14) = -4·s23·s14·(E23·E14)
  -- RHS = t·(2I·(-s12)·E12)·(2I·(-s34)·E34) = t·(-4)·s12·s34·(E12·E34)
  -- E23·E14 = E12·E34 (= E_total), and t = s23·s14/(s12·s34), so both = -4·s23·s14·E_total.
  have hne : s12 * s34 ≠ 0 := ne_of_gt (mul_pos hs12_pos hs34_pos)
  have hne' : (↑s12 : ℂ) * ↑s34 ≠ 0 := by exact_mod_cast hne
  -- Step E: rewrite all differences via hha, then show common phase and scalar equality
  rw [hha θ₂ θ₃, hha θ₁ θ₄, hha θ₁ θ₂, hha θ₃ θ₄]
  simp only [show (θ₁ - θ₂) / 2 = -((θ₂ - θ₁) / 2) from by ring,
             show (θ₃ - θ₄) / 2 = -((θ₄ - θ₃) / 2) from by ring,
             Real.sin_neg]
  push_cast  -- normalize ↑(-s12) → -(↑s12), ↑(-s34) → -(↑s34)
  -- Both sides = 4·I²·↑s23·↑s14·(E12·E34) after using hE and t·s12·s34 = s23·s14
  have hcalc : (↑((-s23) * (-s14) / (s12 * s34)) : ℂ) * (↑s12 * ↑s34) = ↑s23 * ↑s14 := by
    push_cast; field_simp [hne']; ring
  have hLHS : 2 * I * ↑s23 * Complex.exp (↑((θ₂+θ₃)/2) * I) *
              (2 * I * ↑s14 * Complex.exp (↑((θ₁+θ₄)/2) * I)) =
      4 * I ^ 2 * ↑s23 * ↑s14 *
      (Complex.exp (↑((θ₁+θ₂)/2) * I) * Complex.exp (↑((θ₃+θ₄)/2) * I)) :=
    calc _ = 4 * I ^ 2 * ↑s23 * ↑s14 *
              (Complex.exp (↑((θ₂+θ₃)/2) * I) * Complex.exp (↑((θ₁+θ₄)/2) * I)) := by ring
         _ = _ := by rw [hE]
  have hRHS : ↑((-s23) * (-s14) / (s12 * s34)) *
              (2 * I * (-↑s12) * Complex.exp (↑((θ₁+θ₂)/2) * I) *
               (2 * I * (-↑s34) * Complex.exp (↑((θ₃+θ₄)/2) * I))) =
      4 * I ^ 2 * ↑s23 * ↑s14 *
      (Complex.exp (↑((θ₁+θ₂)/2) * I) * Complex.exp (↑((θ₃+θ₄)/2) * I)) :=
    calc _ = 4 * I ^ 2 * (↑((-s23) * (-s14) / (s12 * s34)) * (↑s12 * ↑s34)) *
              (Complex.exp (↑((θ₁+θ₂)/2) * I) * Complex.exp (↑((θ₃+θ₄)/2) * I)) := by
              push_cast; field_simp [hne']; ring
         _ = 4 * I ^ 2 * (↑s23 * ↑s14) * _ := by rw [hcalc]
         _ = _ := by ring
  exact hLHS.trans hRHS.symm

-- ============================================================
-- PART 5: Ptolemy Equality for Unit-Circle CCW Points
-- ============================================================

/-- **Ptolemy's equality for unit-circle CCW points**.

For four unit-circle points in CCW order, Ptolemy's equality holds:
`‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖`.

**Proof**: `ptolemy_ratio_pos_of_ccw` gives `t > 0` with `(z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)`.
Then `ptolemy_equality_of_proportional` (from `PtolemysComplexProof`) with `0 ≤ t` closes the proof. -/
theorem ptolemy_equality_for_unit_circle_ccw (z₁ z₂ z₃ z₄ : ℂ)
    (hccw : IsCCWOrder z₁ z₂ z₃ z₄) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
    ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  obtain ⟨t, ht_pos, ht_eq⟩ := ptolemy_ratio_pos_of_ccw z₁ z₂ z₃ z₄ hccw
  exact ptolemy_equality_of_proportional z₁ z₂ z₃ z₄ t ht_pos.le ht_eq

-- ============================================================
-- PART 6: Concyclicity Definition
-- ============================================================

/-- Four complex numbers are **concyclic** if they lie on a common circle `(c, r)`. -/
def IsConcyclic₄ (z₁ z₂ z₃ z₄ : ℂ) : Prop :=
  ∃ (c : ℂ) (r : ℝ), 0 < r ∧
    ‖z₁ - c‖ = r ∧ ‖z₂ - c‖ = r ∧ ‖z₃ - c‖ = r ∧ ‖z₄ - c‖ = r

-- ============================================================
-- PART 7: Ptolemy for Concyclic Points (Normalization)
-- ============================================================

/-- Normalizing a circle to radius 1 preserves norms. -/
private lemma norm_normalize (z c : ℂ) (r : ℝ) (hr : 0 < r) (hz : ‖z - c‖ = r) :
    ‖(z - c) / (r : ℂ)‖ = 1 := by
  rw [norm_div, hz, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']

/-- Ptolemy equality for concyclic points in CCW order.

For four points on circle `(c, r)` in CCW order (with `wᵢ = (zᵢ - c) / r` in CCW order
on the unit circle), Ptolemy's equality holds.

**Proof**: Normalize to unit circle: `wᵢ = (zᵢ - c) / r`. Then:
- `(zᵢ - c) / r - (zⱼ - c) / r = (zᵢ - zⱼ) / r`, so `‖wᵢ - wⱼ‖ = ‖zᵢ - zⱼ‖ / r`
- `ptolemy_equality_for_unit_circle_ccw` gives Ptolemy equality for the `wᵢ`
- `field_simp` clears the `/ r` denominators to recover equality for the `zᵢ` -/
theorem ptolemy_equality_for_concyclic (z₁ z₂ z₃ z₄ : ℂ) (c : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hc₁ : ‖z₁ - c‖ = r) (hc₂ : ‖z₂ - c‖ = r)
    (hc₃ : ‖z₃ - c‖ = r) (hc₄ : ‖z₄ - c‖ = r)
    (hccw : IsCCWOrder ((z₁ - c) / (r : ℂ)) ((z₂ - c) / (r : ℂ))
                       ((z₃ - c) / (r : ℂ)) ((z₄ - c) / (r : ℂ))) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
    ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  -- Helper: differences of normalized points simplify
  have hdiff : ∀ a b : ℂ,
      (a - c) / (r : ℂ) - (b - c) / (r : ℂ) = (a - b) / (r : ℂ) := by
    intros; field_simp
  -- Apply unit-circle Ptolemy to normalized points
  have hpt := ptolemy_equality_for_unit_circle_ccw
    ((z₁ - c) / (r : ℂ)) ((z₂ - c) / (r : ℂ))
    ((z₃ - c) / (r : ℂ)) ((z₄ - c) / (r : ℂ)) hccw
  -- Rewrite differences and then norms
  rw [hdiff z₁ z₃, hdiff z₂ z₄, hdiff z₁ z₂,
      hdiff z₃ z₄, hdiff z₂ z₃, hdiff z₁ z₄] at hpt
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le] at hpt
  -- hpt : ‖z₁-z₃‖/r * ‖z₂-z₄‖/r = ‖z₁-z₂‖/r * ‖z₃-z₄‖/r + ‖z₂-z₃‖/r * ‖z₁-z₄‖/r
  -- Multiply by r² to clear denominators
  have hr_ne : r ≠ 0 := hr.ne'
  field_simp [hr_ne] at hpt
  linarith

-- ============================================================
-- Summary
-- ============================================================

#check @unit_circle_ptolemy_ratio_real
#check @ptolemy_equality_for_unit_circle_ccw
#check @ptolemy_equality_for_concyclic
