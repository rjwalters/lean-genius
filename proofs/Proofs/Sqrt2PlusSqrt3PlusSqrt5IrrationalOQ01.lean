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

This S2 SCAFFOLD proves three of four supporting lemmas in full and isolates
the algebraic identity `alpha_quartic_identity` as a single `sorry` (the
S3 ACT target). The main theorem `irrational_sqrt2_plus_sqrt3_plus_sqrt5`
is proven modulo `alpha_quartic_identity`, so closing that one `sorry`
in S3 yields a sorry-free / axiom-free verified entry.

## Status
- [x] `irrational_sqrt_thirty`     — proven (one-liner via `irrational_sqrt_natCast_iff`)
- [x] `alpha_pos`                  — proven (`linarith` on three `sqrt_nonneg/pos`)
- [ ] `alpha_quartic_identity`     — **`sorry`** (deferred to S3; proof sketch in docstring)
- [x] `irrational_sqrt2_plus_sqrt3_plus_sqrt5` — proven **modulo** `alpha_quartic_identity`
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

/-- The key quartic identity:
    `(√2 + √3 + √5)⁴ - 20·(√2 + √3 + √5)² - 24 = 8·(√2 + √3 + √5)·√30`.

**Proof sketch (S3 ACT target).**
Let α := √2 + √3 + √5. The chain is

    (α - √5)² = (√2 + √3)² = 5 + 2√6      (parent identity)
    α² = 2α√5 + 2√6                        (rearrange + (√5)² = 5)
    α⁴ = (2α√5 + 2√6)²
       = 4α²·5 + 8α·√5√6 + 4·6
       = 20α² + 8α·√30 + 24                ((√5)² = 5, (√6)² = 6, √5·√6 = √30)

The single-tactic `linear_combination` discharge should be:

```lean
  -- hkey : α^2 = 2*α*sqrt 5 + 2*sqrt 6
  -- h5sq : sqrt 5 * sqrt 5 = 5
  -- h6sq : sqrt 6 * sqrt 6 = 6
  -- h56  : sqrt 5 * sqrt 6 = sqrt 30
  linear_combination
        (α^2 + 2*α*sqrt 5 + 2*sqrt 6) * hkey
      + (4*α^2) * h5sq
      + (8*α)   * h56
      + 4       * h6sq
```

Algebra check (treating √5, √6, √30, α as independent indeterminates):

    (α² + 2α√5 + 2√6)·(α² - 2α√5 - 2√6) = α⁴ - 4α²(√5)² - 8α(√5)(√6) - 4(√6)²
    + 4α²·((√5)² - 5)                     = 4α²(√5)² - 20α²
    + 8α·((√5)(√6) - √30)                 = 8α(√5)(√6) - 8α√30
    + 4·((√6)² - 6)                       = 4(√6)² - 24

    Sum: α⁴ - 20α² - 8α√30 - 24
       = (α⁴ - 20α² - 24) - 8α√30 ✓

(Verified by symbolic expansion above. Deferred to S3 because the
Docker build needed to confirm `linear_combination` accepts these
coefficients is a separate iteration.) -/
theorem alpha_quartic_identity :
    (sqrt 2 + sqrt 3 + sqrt 5) ^ 4
      - 20 * (sqrt 2 + sqrt 3 + sqrt 5) ^ 2 - 24
      = 8 * (sqrt 2 + sqrt 3 + sqrt 5) * sqrt 30 := by
  -- See docstring: discharge via the four-term `linear_combination`
  -- after establishing `hkey`, `h5sq`, `h6sq`, `h56`.
  sorry

/-- **Main theorem (modulo `alpha_quartic_identity`)**:
`√2 + √3 + √5` is irrational. -/
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
