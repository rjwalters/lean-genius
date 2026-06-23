import Mathlib

/-
# Closed-Form Product Formula for the Buffon Crossing Factor
# (buffons-needle-oq-02-oq-02-oq-01-oq-01)

## The Open Question

The n-dimensional Buffon noodle formula `E[crossings] = αₙ · L/d` is governed by
the **crossing factor** `αₙ = E_{Sⁿ⁻¹}[|u₁|]`, defined by the two-step recurrence
`α_{n+2} = (n/(n+1)) · αₙ` with base values `α₂ = 2/π` and `α₃ = 1/2`. The parent
entry `buffons-needle-oq-02-oq-02-oq-01` proves the *structural* monotonicity of
`αₙ` (strict two-step decrease, maximum `2/π`, uniform sub-one bound) directly
from the recurrence, but never solves the recurrence: it leaves open the explicit
**closed form** of the even- and odd-dimension subsequences.

## Result

We *solve* the two-step recurrence, giving the exact telescoping products that
unfold it. Writing the recurrence factors out, every even (resp. odd) dimension
is the base value `2/π` (resp. `1/2`) times a finite product of the rational
ratios `(2j+2)/(2j+3)` (resp. `(2j+3)/(2j+4)`):

1. `crossingFactor_even` — **even subsequence closed form**:
   `α_{2m+2} = (2/π) · ∏_{j<m} (2j+2)/(2j+3)`.

2. `crossingFactor_odd` — **odd subsequence closed form**:
   `α_{2m+3} = (1/2) · ∏_{j<m} (2j+3)/(2j+4)`.

3. `crossingFactor_even_pos` / `crossingFactor_even_le_base` — each product factor
   lies in `(0,1]`, so the formula re-derives positivity and the maximum `2/π`
   for the even subsequence *from the closed form*.

4. `crossingFactor_four`, `crossingFactor_six`, `crossingFactor_five`,
   `crossingFactor_seven` — the first higher concrete values
   `α₄ = 4/(3π)`, `α₆ = 16/(15π)`, `α₅ = 3/8`, `α₇ = 5/16`, evaluated directly
   from the product formula (none are computed in the parent).

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace BuffonsNeedleOQ02OQ02OQ01OQ01

open Real

/-- The n-dimensional crossing factor `αₙ = E_{Sⁿ⁻¹}[|u₁|]`, by the recurrence
    `α_{n+2} = (n/(n+1)) · αₙ` with `α₂ = 2/π`, `α₃ = 1/2` (and `1` for `n ≤ 1`
    by convention). Re-declared verbatim from `BuffonsNeedleOQ02OQ01.lean`, whose
    companion currently fails to build on the pinned Mathlib. -/
noncomputable def crossingFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2 / π
  | 3 => 1 / 2
  | (n + 4) => ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2)

@[simp] lemma crossingFactor_two : crossingFactor 2 = 2 / π := rfl

@[simp] lemma crossingFactor_three : crossingFactor 3 = 1 / 2 := rfl

/-- The fundamental recurrence `α_{n+4} = ((n+2)/(n+3)) · α_{n+2}`. -/
@[simp] lemma crossingFactor_succ_succ (n : ℕ) :
    crossingFactor (n + 4) = ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2) := rfl

-- ============================================================
-- PART 1: The closed-form product formulas
-- ============================================================

/-- **Even-dimension closed form.** Solving the two-step recurrence on the even
    subsequence: `α_{2m+2} = (2/π) · ∏_{j<m} (2j+2)/(2j+3)`. The empty product
    (`m = 0`) recovers `α₂ = 2/π`, and each step appends the recurrence factor. -/
theorem crossingFactor_even (m : ℕ) :
    crossingFactor (2 * m + 2)
      = (2 / π) * ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) := by
  induction m with
  | zero =>
      show crossingFactor 2 = (2 / π) * ∏ j ∈ Finset.range 0, (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)
      rw [Finset.prod_range_zero, mul_one, crossingFactor_two]
  | succ k ih =>
      have hidx : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
      rw [hidx, crossingFactor_succ_succ (2 * k), ih, Finset.prod_range_succ]
      push_cast
      ring

/-- **Odd-dimension closed form.** Solving the two-step recurrence on the odd
    subsequence: `α_{2m+3} = (1/2) · ∏_{j<m} (2j+3)/(2j+4)`. The empty product
    (`m = 0`) recovers `α₃ = 1/2`, and each step appends the recurrence factor. -/
theorem crossingFactor_odd (m : ℕ) :
    crossingFactor (2 * m + 3)
      = (1 / 2) * ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 4) := by
  induction m with
  | zero =>
      show crossingFactor 3 = (1 / 2) * ∏ j ∈ Finset.range 0, (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 4)
      rw [Finset.prod_range_zero, mul_one, crossingFactor_three]
  | succ k ih =>
      have hidx : 2 * (k + 1) + 3 = (2 * k + 1) + 4 := by ring
      have hidx2 : (2 * k + 1) + 2 = 2 * k + 3 := by ring
      rw [hidx, crossingFactor_succ_succ (2 * k + 1), hidx2, ih, Finset.prod_range_succ]
      push_cast
      ring

-- ============================================================
-- PART 2: Positivity and the maximum, re-derived from the product
-- ============================================================

/-- Each even-subsequence factor is positive. -/
lemma evenFactor_pos (j : ℕ) : 0 < (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) := by
  positivity

/-- Each even-subsequence factor is at most one (`(2j+2)/(2j+3) ≤ 1`). -/
lemma evenFactor_le_one (j : ℕ) : (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) j]

/-- **Positivity from the closed form.** `0 < α_{2m+2}`, since `2/π > 0` and the
    product is a finite product of positive factors. -/
theorem crossingFactor_even_pos (m : ℕ) : 0 < crossingFactor (2 * m + 2) := by
  rw [crossingFactor_even]
  apply mul_pos (by positivity)
  apply Finset.prod_pos
  intro j _
  exact evenFactor_pos j

/-- **The maximum `2/π`, from the closed form.** `α_{2m+2} ≤ 2/π`, since the
    product of factors each `≤ 1` is itself `≤ 1`. -/
theorem crossingFactor_even_le_base (m : ℕ) : crossingFactor (2 * m + 2) ≤ 2 / π := by
  rw [crossingFactor_even]
  nth_rewrite 2 [← mul_one (2 / π)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∏ j ∈ Finset.range m, (2 * (j : ℝ) + 2) / (2 * (j : ℝ) + 3)
      ≤ ∏ _j ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro j _; exact (evenFactor_pos j).le
        · intro j _; exact evenFactor_le_one j
    _ = 1 := by rw [Finset.prod_const_one]

-- ============================================================
-- PART 3: Concrete higher values, evaluated from the product
-- ============================================================

/-- `α₄ = 4/(3π)` — the first even value past the base, from the product formula. -/
theorem crossingFactor_four : crossingFactor 4 = 4 / (3 * π) := by
  have h := crossingFactor_even 1
  rw [Finset.prod_range_one] at h
  rw [show (4 : ℕ) = 2 * 1 + 2 from rfl, h]
  push_cast; ring

/-- `α₆ = 16/(15π)` — the second even value, from the product formula. -/
theorem crossingFactor_six : crossingFactor 6 = 16 / (15 * π) := by
  have h := crossingFactor_even 2
  rw [Finset.prod_range_succ, Finset.prod_range_one] at h
  rw [show (6 : ℕ) = 2 * 2 + 2 from rfl, h]
  push_cast; ring

/-- `α₅ = 3/8` — the first odd value past the base, from the product formula. -/
theorem crossingFactor_five : crossingFactor 5 = 3 / 8 := by
  have h := crossingFactor_odd 1
  rw [Finset.prod_range_one] at h
  rw [show (5 : ℕ) = 2 * 1 + 3 from rfl, h]
  push_cast; ring

/-- `α₇ = 5/16` — the second odd value, from the product formula. -/
theorem crossingFactor_seven : crossingFactor 7 = 5 / 16 := by
  have h := crossingFactor_odd 2
  rw [Finset.prod_range_succ, Finset.prod_range_one] at h
  rw [show (7 : ℕ) = 2 * 2 + 3 from rfl, h]
  push_cast; ring

/-
## Significance

The parent entry establishes the *qualitative* monotone behaviour of the Buffon
crossing factor `αₙ = E_{Sⁿ⁻¹}[|u₁|]` directly from its two-step recurrence
`α_{n+2} = (n/(n+1))αₙ`. This entry *solves* that recurrence in closed form: the
even and odd subsequences are the base values `2/π` and `1/2` times explicit
telescoping products of the rational factors `(2j+2)/(2j+3)` and `(2j+3)/(2j+4)`
(`crossingFactor_even`, `crossingFactor_odd`). These are the finite Wallis-type
partial products underlying the exact value `αₙ = Γ(n/2)/(√π Γ((n+1)/2))`.

The closed form makes the structural facts transparent: positivity and the
maximum `2/π` follow because the products are built from factors in `(0,1]`
(`crossingFactor_even_pos`, `crossingFactor_even_le_base`), and the higher values
`α₄ = 4/(3π)`, `α₆ = 16/(15π)`, `α₅ = 3/8`, `α₇ = 5/16` drop out by direct
evaluation (`crossingFactor_four`, `crossingFactor_six`, `crossingFactor_five`,
`crossingFactor_seven`). Everything is verified from the recurrence and its base
values, with no axioms.
-/

end BuffonsNeedleOQ02OQ02OQ01OQ01
