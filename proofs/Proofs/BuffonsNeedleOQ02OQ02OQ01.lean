import Mathlib

/-
# Monotonicity of the Buffon Crossing Factor in the Dimension
# (buffons-needle-oq-02-oq-02-oq-01)

## The Open Question

The n-dimensional Buffon noodle formula `E[crossings] = αₙ · L/d` is governed by
the **crossing factor** `αₙ = E_{Sⁿ⁻¹}[|u₁|]`, defined by the recurrence
`α_{n+2} = (n/(n+1)) · αₙ` with base values `α₂ = 2/π` and `α₃ = 1/2`. The
companion file `BuffonsNeedleOQ02OQ01.lean` records individual values and
positivity, but leaves open the **global monotone behaviour**: how does the
geometric thinning of crossings vary with dimension?

## Result

We prove the crossing factor's structural monotonicity. (The companion file is
self-contained-reproduced here: it currently fails to build on the pinned Mathlib
— a `Filter.Tendsto.div` API drift — so the recurrence and its base facts are
re-declared verbatim.)

1. `crossingFactor_two_step_lt` — **strict two-step decrease**: `α_{n+2} < αₙ`
   for `n ≥ 2`. Each recurrence step multiplies the positive `αₙ` by
   `n/(n+1) < 1`.

2. `crossingFactor_le_two_div_pi` — **the maximum is `α₂ = 2/π`**:
   `αₙ ≤ 2/π` for all `n ≥ 2`. Both the even and odd subsequences start at their
   largest value and decrease.

3. `crossingFactor_lt_one` — consequently `αₙ < 1` for all `n ≥ 2`: in every
   dimension the expected crossings per unit `L/d` are *less than one*
   (`2/π < 1`).

4. `crossingFactor_three_lt_two` — the first comparison `α₃ < α₂` made concrete
   (`1/2 < 2/π`), the seed of the odd-versus-even interleaving.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace BuffonsNeedleOQ02OQ02OQ01

open Real

/-- The n-dimensional crossing factor `αₙ = E_{Sⁿ⁻¹}[|u₁|]`, by the recurrence
    `α_{n+2} = (n/(n+1)) · αₙ` with `α₂ = 2/π`, `α₃ = 1/2` (and `1` for `n ≤ 1`
    by convention). Re-declared verbatim from `BuffonsNeedleOQ02OQ01.lean`. -/
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

/-- The crossing factor is positive for every `n ≥ 2`. -/
theorem crossingFactor_pos : ∀ n : ℕ, 2 ≤ n → 0 < crossingFactor n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · rw [crossingFactor_two]; positivity
      · rw [crossingFactor_three]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [crossingFactor_succ_succ]
      exact mul_pos (by positivity) (ih (m + 2) (by omega) (by omega))

-- ============================================================
-- PART 1: Strict two-step monotonicity
-- ============================================================

/-- **The crossing factor strictly decreases by two dimensions.** For `n ≥ 2`,
    `α_{n+2} < αₙ`: the recurrence multiplies `αₙ` (positive) by `n/(n+1) < 1`. -/
theorem crossingFactor_two_step_lt (n : ℕ) (hn : 2 ≤ n) :
    crossingFactor (n + 2) < crossingFactor n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 + 2 = m + 4 from rfl, crossingFactor_succ_succ]
  have hpos : 0 < crossingFactor (m + 2) := crossingFactor_pos (m + 2) (by omega)
  have hratio : (m + 2 : ℝ) / (m + 3) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  nlinarith [hpos, hratio, mul_pos hpos (by linarith : (0:ℝ) < 1 - (m + 2) / (m + 3))]

/-- The first concrete comparison `α₃ < α₂`, i.e. `1/2 < 2/π` (since `π < 4`). -/
theorem crossingFactor_three_lt_two : crossingFactor 3 < crossingFactor 2 := by
  rw [crossingFactor_three, crossingFactor_two, lt_div_iff₀ pi_pos]
  linarith [pi_lt_four]

-- ============================================================
-- PART 2: The maximum is α₂ = 2/π, hence αₙ < 1
-- ============================================================

/-- **The crossing factor is maximized at `n = 2`.** `αₙ ≤ 2/π` for all `n ≥ 2`,
    by two-step descent from the base values `α₂ = 2/π` and `α₃ = 1/2 ≤ 2/π`. -/
theorem crossingFactor_le_two_div_pi (n : ℕ) (hn : 2 ≤ n) :
    crossingFactor n ≤ 2 / π := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · rw [crossingFactor_two]
      · rw [crossingFactor_three, le_div_iff₀ pi_pos]
        linarith [pi_le_four]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [crossingFactor_succ_succ]
      have ihm : crossingFactor (m + 2) ≤ 2 / π := ih (m + 2) (by omega) (by omega)
      have hpos : 0 < crossingFactor (m + 2) := crossingFactor_pos (m + 2) (by omega)
      have hratio : (m + 2 : ℝ) / (m + 3) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith [ihm, hpos, hratio,
        mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (m + 2) / (m + 3)) hpos.le]

/-- **In every dimension the crossing factor is below one.** `αₙ < 1` for all
    `n ≥ 2`, since `αₙ ≤ 2/π < 1` (because `2 < π`). The expected crossings per
    unit `L/d` never reach one. -/
theorem crossingFactor_lt_one (n : ℕ) (hn : 2 ≤ n) : crossingFactor n < 1 := by
  have h := crossingFactor_le_two_div_pi n hn
  have hlt : (2 : ℝ) / π < 1 := by
    rw [div_lt_one pi_pos]; linarith [pi_gt_three]
  linarith

/-
## Significance

The n-dimensional Buffon noodle constant `αₙ = E_{Sⁿ⁻¹}[|u₁|]` measures how the
expected number of hyperplane crossings of a unit-length curve thins as the
ambient dimension grows: a random direction's first coordinate concentrates near
`0`, so `αₙ → 0`. The recurrence pins down the values and positivity but not the
global monotone picture.

This entry supplies it: `αₙ` strictly decreases in two-dimension steps
(`crossingFactor_two_step_lt`), is maximized at the classical Buffon value
`α₂ = 2/π` (`crossingFactor_le_two_div_pi`), and is therefore uniformly below one
in every dimension (`crossingFactor_lt_one`). The two-step structure reflects the
even/odd interleaving of the recurrence — both subsequences descend from their
first term, with the odd one already starting below the even one
(`crossingFactor_three_lt_two`). Everything is verified from the recurrence and
its base values, with no axioms.
-/

end BuffonsNeedleOQ02OQ02OQ01
