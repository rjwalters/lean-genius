import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

/-
# Machin's Formula from the Arctan Addition Formula

## What This Proves

Machin's formula (1706):
  π/4 = 4·arctan(1/5) - arctan(1/239)

derived step by step from the arctan addition formula:
  arctan(x) + arctan(y) = arctan((x+y)/(1-xy))  when xy < 1

## Approach

Three applications of the addition formula:
1. arctan(1/5) + arctan(1/5) = arctan(5/12)
2. arctan(5/12) + arctan(5/12) = arctan(120/119)
3. arctan(120/119) + arctan(-1/239) = arctan(1) = π/4

## Why This Matters

Machin used this identity in 1706 to compute 100 digits of π — a record
at the time. The key insight is that arctan(1/5) converges much faster than
the Leibniz series (arctan at 1). Each step is a pure algebraic consequence
of the addition formula.

This proof does NOT use Mathlib's pre-packaged
`Real.four_mul_arctan_inv_5_sub_arctan_inv_239`. Instead, it derives
the identity from scratch using only `Real.arctan_add`, `Real.arctan_neg`,
and `Real.arctan_one`.
-/

namespace MachinFromAddition

open Real

/-- **Step 1**: Two applications of arctan(1/5) yield arctan(5/12).

    arctan(1/5) + arctan(1/5) = arctan((1/5 + 1/5) / (1 - 1/5 · 1/5))
                               = arctan((2/5) / (24/25))
                               = arctan(5/12) -/
theorem two_arctan_inv_5 :
    arctan (1 / 5 : ℝ) + arctan (1 / 5 : ℝ) = arctan (5 / 12 : ℝ) := by
  rw [arctan_add (by norm_num : (1 / 5 : ℝ) * (1 / 5) < 1)]
  congr 1
  norm_num

/-- **Step 2**: Four applications of arctan(1/5) yield arctan(120/119).

    4·arctan(1/5) = 2·(2·arctan(1/5))
                  = 2·arctan(5/12)
                  = arctan((5/12 + 5/12) / (1 - 5/12 · 5/12))
                  = arctan((10/12) / (119/144))
                  = arctan(120/119) -/
theorem four_arctan_inv_5 :
    4 * arctan (1 / 5 : ℝ) = arctan (120 / 119 : ℝ) := by
  have h := two_arctan_inv_5
  have : 4 * arctan (1 / 5 : ℝ) = (arctan (1 / 5 : ℝ) + arctan (1 / 5 : ℝ)) +
                                    (arctan (1 / 5 : ℝ) + arctan (1 / 5 : ℝ)) := by ring
  rw [this, h, arctan_add (by norm_num : (5 / 12 : ℝ) * (5 / 12) < 1)]
  congr 1
  norm_num

/-- **Step 3**: Subtracting arctan(1/239) from arctan(120/119) gives arctan(1).

    arctan(120/119) - arctan(1/239)
      = arctan(120/119) + arctan(-1/239)
      = arctan((120/119 - 1/239) / (1 + 120/(119·239)))
      = arctan((28561/28441) / (28561/28441))
      = arctan(1)

    The numerator and denominator are both 28561/28441 = 169²/(119·239),
    so the ratio is exactly 1. -/
theorem arctan_diff_eq_arctan_one :
    arctan (120 / 119 : ℝ) - arctan (1 / 239 : ℝ) = arctan (1 : ℝ) := by
  have h : arctan (120 / 119 : ℝ) - arctan (1 / 239 : ℝ) =
           arctan (120 / 119 : ℝ) + arctan (-(1 / 239) : ℝ) := by
    rw [arctan_neg]; ring
  rw [h, arctan_add (by norm_num : (120 / 119 : ℝ) * (-(1 / 239)) < 1)]
  congr 1
  norm_num

/-- **Machin's Formula** (1706):

    π/4 = 4·arctan(1/5) - arctan(1/239)

    Proved from scratch using three applications of the arctan addition formula.
    This was the identity John Machin used to compute 100 digits of π,
    making it the most precise computation of its era. -/
theorem machin_formula :
    4 * arctan (1 / 5 : ℝ) - arctan (1 / 239 : ℝ) = π / 4 := by
  rw [four_arctan_inv_5, arctan_diff_eq_arctan_one, arctan_one]

end MachinFromAddition
