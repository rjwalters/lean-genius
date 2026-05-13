/-
# Irrationality of √2 + √3 + √5 (OQ-01 of `sqrt2-plus-sqrt3-irrational`)

## Strategy — isolate √30 by squaring twice

Let α := √2 + √3 + √5. Assume α = r ∈ ℚ. We derive √30 ∈ ℚ, contradicting
irrationality of √30 (since 30 is not a perfect square).

**Step 1 (subtract √5, then square once).** Using the parent identity
`(√2 + √3)² = 5 + 2√6` (`Sqrt2PlusSqrt3Irrational.sqrt2_plus_sqrt3_sq`)
and `(√5)² = 5`:

    (α - √5)² = (√2 + √3)² = 5 + 2√6
    α² - 2α√5 + 5 = 5 + 2√6
    α² = 2α√5 + 2√6                           (*)

**Step 2 (square once more).** Squaring (*) and using `(√5)² = 5`,
`(√6)² = 6`, `√5·√6 = √30`:

    α⁴ = (2α√5 + 2√6)² = 4α²·5 + 8α·√5√6 + 4·6
       = 20α² + 8α·√30 + 24

So `α⁴ - 20α² - 24 = 8α·√30`           (**)

**Step 3 (divide & conclude).** Since α ≥ √5 > 0, we have 8α ≠ 0, so

    √30 = (α⁴ - 20α² - 24) / (8α)

which is rational if α is rational. Contradiction.

## File layout

This S2 ACT proves all four supporting lemmas in full. The quartic
identity uses the two-substitution + linear-arithmetic chain locked
in by the S2 PREP iteration (#18353 sessions doc).

## Status
- [x] `irrational_sqrt_thirty`     — proven (one-liner via `irrational_sqrt_natCast_iff`)
- [x] `alpha_pos`                  — proven (`linarith` on three `sqrt_nonneg/pos`)
- [x] `alpha_quartic_identity`     — proven (parent-identity reuse + `Real.sq_sqrt` × 2 + cross-radical bridge `√5·√6 = √30`)
- [x] `irrational_sqrt2_plus_sqrt3_plus_sqrt5` — proven (`eq_div_iff` + `push_cast` + `irrational_sqrt_thirty`)
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Proofs.Sqrt2PlusSqrt3Irrational

open Real

namespace Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01

/-- `√30` is irrational (30 is not a perfect square). -/
theorem irrational_sqrt_thirty : Irrational (sqrt 30) := by
  have hns : ¬ IsSquare (30 : ℕ) := by native_decide
  exact irrational_sqrt_natCast_iff.mpr hns

/-- Positivity: `0 < √2 + √3 + √5`. We need this so that `8·α ≠ 0` in
the main theorem, which lets us divide by `8α`. -/
theorem alpha_pos : (0 : ℝ) < sqrt 2 + sqrt 3 + sqrt 5 := by
  have h2 : (0 : ℝ) ≤ sqrt 2 := sqrt_nonneg 2
  have h3 : (0 : ℝ) ≤ sqrt 3 := sqrt_nonneg 3
  have h5 : (0 : ℝ) < sqrt 5 := sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  linarith

/-- Cross-radical bridge: `√5 · √6 = √30`. -/
private theorem sqrt5_mul_sqrt6 : sqrt 5 * sqrt 6 = sqrt 30 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- The key quartic identity:
    `(√2 + √3 + √5)⁴ - 20·(√2 + √3 + √5)² - 24 = 8·(√2 + √3 + √5)·√30`.

Proof chain (locked in by PR #18353 S2 PREP):
    (α - √5)² = (√2 + √3)² = 5 + 2√6      (parent identity)
    α² = 2α√5 + 2√6                        (rearrange + (√5)² = 5)
    α⁴ = (2α√5 + 2√6)²
       = 4α²·5 + 8α·√5√6 + 4·6
       = 20α² + 8α·√30 + 24                ((√5)² = 5, (√6)² = 6, √5·√6 = √30)
-/
theorem alpha_quartic_identity :
    (sqrt 2 + sqrt 3 + sqrt 5) ^ 4
      - 20 * (sqrt 2 + sqrt 3 + sqrt 5) ^ 2 - 24
      = 8 * (sqrt 2 + sqrt 3 + sqrt 5) * sqrt 30 := by
  set α := sqrt 2 + sqrt 3 + sqrt 5 with hα
  -- Step 1: (α - √5)² = (√2 + √3)² = 5 + 2√6 (parent identity).
  have h1 : (α - sqrt 5) ^ 2 = 5 + 2 * sqrt 6 := by
    have hαsub : α - sqrt 5 = sqrt 2 + sqrt 3 := by rw [hα]; ring
    rw [hαsub]
    exact Sqrt2PlusSqrt3Irrational.sqrt2_plus_sqrt3_sq
  -- Expand (α - √5)² = α² - 2α√5 + (√5)² and use (√5)² = 5.
  have h5sq : sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have h1' : α ^ 2 - 2 * α * sqrt 5 - 2 * sqrt 6 = 0 := by
    have hexp : (α - sqrt 5) ^ 2 = α ^ 2 - 2 * α * sqrt 5 + sqrt 5 ^ 2 := by ring
    rw [hexp, h5sq] at h1
    linarith
  -- Rearrange: α² = 2α√5 + 2√6.
  have h_alpha_sq : α ^ 2 = 2 * α * sqrt 5 + 2 * sqrt 6 := by linarith
  -- Step 2: square the rearrangement to isolate √30.
  have h_sq : (α ^ 2) ^ 2 = (2 * α * sqrt 5 + 2 * sqrt 6) ^ 2 := by
    rw [h_alpha_sq]
  -- Expand the RHS symbolically, then use the cross-radical bridge.
  have h6sq : sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have h_rhs :
      (2 * α * sqrt 5 + 2 * sqrt 6) ^ 2
        = 4 * α ^ 2 * (sqrt 5 ^ 2)
          + 8 * α * (sqrt 5 * sqrt 6) + 4 * (sqrt 6 ^ 2) := by ring
  rw [h_rhs, h5sq, h6sq, sqrt5_mul_sqrt6] at h_sq
  -- h_sq : (α^2)^2 = 4·α²·5 + 8·α·√30 + 4·6 = 20·α² + 8·α·√30 + 24
  have hα4 : α ^ 4 = 20 * α ^ 2 + 8 * α * sqrt 30 + 24 := by
    have epow : (α ^ 2) ^ 2 = α ^ 4 := by ring
    linarith [h_sq, epow]
  linarith

/-- **Main theorem**: `√2 + √3 + √5` is irrational. -/
theorem irrational_sqrt2_plus_sqrt3_plus_sqrt5 :
    Irrational (sqrt 2 + sqrt 3 + sqrt 5) := by
  intro ⟨r, hr⟩
  -- hr : (r : ℝ) = sqrt 2 + sqrt 3 + sqrt 5
  -- Positivity: α > 0.
  have hpos : (0 : ℝ) < sqrt 2 + sqrt 3 + sqrt 5 := alpha_pos
  have hαne : sqrt 2 + sqrt 3 + sqrt 5 ≠ 0 := ne_of_gt hpos
  -- The quartic identity.
  have hkey : (sqrt 2 + sqrt 3 + sqrt 5) ^ 4
                - 20 * (sqrt 2 + sqrt 3 + sqrt 5) ^ 2 - 24
              = 8 * (sqrt 2 + sqrt 3 + sqrt 5) * sqrt 30 :=
    alpha_quartic_identity
  -- Substitute r for α: get a polynomial relation in (r : ℝ).
  have hkey_r : (r : ℝ) ^ 4 - 20 * (r : ℝ) ^ 2 - 24 = 8 * (r : ℝ) * sqrt 30 := by
    rw [hr]; exact hkey
  -- (r : ℝ) ≠ 0, since the LHS of `hr` is positive.
  have hr_ne : (r : ℝ) ≠ 0 := by
    rw [hr]; exact hαne
  -- 8·(r : ℝ) ≠ 0.
  have h8r_ne : (8 : ℝ) * (r : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hr_ne
  -- Divide: √30 = (r⁴ - 20r² - 24) / (8r) in ℝ.
  have hsqrt30 : sqrt 30 = ((r : ℝ) ^ 4 - 20 * (r : ℝ) ^ 2 - 24) / (8 * (r : ℝ)) := by
    rw [eq_div_iff h8r_ne, hkey_r]; ring
  -- Exhibit a rational equal to √30, contradicting `irrational_sqrt_thirty`.
  refine irrational_sqrt_thirty ⟨(r ^ 4 - 20 * r ^ 2 - 24) / (8 * r), ?_⟩
  push_cast
  exact hsqrt30.symm

end Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01
