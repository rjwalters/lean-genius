import Proofs.BuffonsNeedleOQ02OQ01

/-
# Closed Form for the n-Dimensional Buffon Crossing Factor αₙ

## What This Proves

The parent file `BuffonsNeedleOQ02OQ01.lean` defines the n-dimensional Buffon
crossing factor `crossingFactor n = αₙ` recursively:

  α₂ = 2/π,   α₃ = 1/2,   α_{n+4} = ((n+2)/(n+3)) · α_{n+2}.

This file solves that recurrence in **closed form** using Gamma-function values,
replacing the per-dimension recurrence with a single explicit formula
(the Cauchy–Crofton / integral-geometry lineage):

  **αₙ = Γ(n/2) / (√π · Γ((n+1)/2))    for all n ≥ 2.**

This is the sphere-average identity αₙ = E_{S^{n-1}}[|u₁|] evaluated via the
Beta/Gamma integral, and it settles the open question of expressing αₙ without
recursion.

## Proof Strategy

We define `gammaForm n = Γ(n/2) / (√π · Γ((n+1)/2))` and prove
`crossingFactor n = gammaForm n` for `n ≥ 2` by the same two-step induction used
for the recurrence:

* **Base cases** `n = 2, 3`: direct evaluation using `Γ(1) = 1`,
  `Γ(3/2) = √π/2`, `Γ(2) = 1`.
* **Inductive step**: `gammaForm` obeys the *same* recurrence
  `gammaForm (k+2) = (k/(k+1)) · gammaForm k` (Lemma `gammaForm_rec`), which is a
  one-line consequence of the functional equation `Γ(x+1) = x·Γ(x)`
  (`Real.Gamma_add_one`). Matching base cases + matching recurrence ⟹ equal.

Both are self-contained, Mathlib-only, and fully verified (no `sorry`, no axioms).

## Connection to Prior Work

- `BuffonsNeedleOQ02OQ01.lean`: defines `crossingFactor`, proves the recurrence,
  computed values α₄ = 4/(3π), α₅ = 3/8, monotonicity, and αₙ → 0.
- **This file**: the exact Gamma closed form, from which every computed value
  follows by a single Gamma evaluation.
-/

namespace BuffonsNeedleOQ02OQ01OQ01

open Real BuffonsNeedleOQ02OQ01

-- ============================================================
-- Part I: The Gamma Closed Form
-- ============================================================

/-- The closed-form candidate for the crossing factor:
    `αₙ = Γ(n/2) / (√π · Γ((n+1)/2))`.
    This is the sphere-average `E_{S^{n-1}}[|u₁|]` written via Gamma values. -/
noncomputable def gammaForm (n : ℕ) : ℝ :=
  Real.Gamma ((n : ℝ) / 2) / (Real.sqrt π * Real.Gamma (((n : ℝ) + 1) / 2))

-- ============================================================
-- Part II: Gamma Values Needed for the Base Cases
-- ============================================================

/-- `Γ(3/2) = √π / 2`, from `Γ(x+1) = x·Γ(x)` and `Γ(1/2) = √π`. -/
lemma gamma_three_half : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  ring

/-- `Γ(2) = 1`, from `Γ(x+1) = x·Γ(x)` and `Γ(1) = 1`. -/
lemma gamma_two : Real.Gamma 2 = 1 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (one_ne_zero), Real.Gamma_one]
  ring

-- ============================================================
-- Part III: `gammaForm` Obeys the Buffon Recurrence
-- ============================================================

/-- The closed form satisfies exactly the crossing-factor recurrence:
    `gammaForm (k+2) = (k/(k+1)) · gammaForm k` for `k ≥ 1`.
    Proof: `Γ((k+2)/2) = (k/2)·Γ(k/2)` and `Γ((k+3)/2) = ((k+1)/2)·Γ((k+1)/2)`
    by the Gamma functional equation, then simplify. -/
lemma gammaForm_rec (k : ℕ) (hk : k ≠ 0) :
    gammaForm (k + 2) = ((k : ℝ) / ((k : ℝ) + 1)) * gammaForm k := by
  unfold gammaForm
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hkhalf : (k : ℝ) / 2 ≠ 0 := div_ne_zero hk0 two_ne_zero
  have hk1half : ((k : ℝ) + 1) / 2 ≠ 0 := by positivity
  -- Rewrite the two Gamma arguments of `gammaForm (k+2)` as "· + 1".
  have a1 : ((k + 2 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 := by push_cast; ring
  have a2 : (((k + 2 : ℕ) : ℝ) + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 := by push_cast; ring
  rw [a1, a2, Real.Gamma_add_one hkhalf, Real.Gamma_add_one hk1half]
  -- Algebraic simplification.
  have hs : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
  have hB : Real.Gamma (((k : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

-- ============================================================
-- Part IV: Main Theorem — Recurrence = Closed Form
-- ============================================================

/-- **Main result.** The recursively-defined crossing factor equals the Gamma
    closed form for every dimension `n ≥ 2`:

      `crossingFactor n = Γ(n/2) / (√π · Γ((n+1)/2))`.

    Proved by two-step induction: base cases `n = 2, 3` by direct evaluation, and
    the step because both sides obey the recurrence `α_{k+2} = (k/(k+1))·α_k`. -/
theorem crossingFactor_eq_gammaForm : ∀ n : ℕ, 2 ≤ n → crossingFactor n = gammaForm n
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by
      rw [crossingFactor_two]
      unfold gammaForm
      rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num,
          show (((2 : ℕ) : ℝ) + 1) / 2 = 3 / 2 by norm_num,
          Real.Gamma_one, gamma_three_half]
      -- goal: 2/π = 1 / (√π * (√π/2))
      rw [show Real.sqrt π * (Real.sqrt π / 2) = π / 2 by
            rw [← mul_div_assoc, Real.mul_self_sqrt pi_pos.le],
          one_div_div]
  | 3, _ => by
      rw [crossingFactor_three]
      unfold gammaForm
      rw [show ((3 : ℕ) : ℝ) / 2 = 3 / 2 by norm_num,
          show (((3 : ℕ) : ℝ) + 1) / 2 = 2 by norm_num,
          gamma_three_half, gamma_two]
      -- goal: 1/2 = (√π/2) / (√π * 1)
      have hs : Real.sqrt π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr pi_pos)
      rw [mul_one, div_right_comm, div_self hs]
  | (n + 4), _ => by
      rw [crossingFactor_succ_succ, crossingFactor_eq_gammaForm (n + 2) (by omega)]
      -- goal: ((n+2)/(n+3)) * gammaForm (n+2) = gammaForm (n+4)
      conv_rhs => rw [show n + 4 = (n + 2) + 2 from rfl, gammaForm_rec (n + 2) (by omega)]
      push_cast
      ring

-- ============================================================
-- Part V: The Closed Form, Cleanly Stated
-- ============================================================

/-- **Explicit closed form** for the n-dimensional Buffon crossing factor:

      `αₙ = Γ(n/2) / (√π · Γ((n+1)/2))    (n ≥ 2)`,

    with no recursion. -/
theorem crossingFactor_closed_form (n : ℕ) (hn : 2 ≤ n) :
    crossingFactor n =
      Real.Gamma ((n : ℝ) / 2) / (Real.sqrt π * Real.Gamma (((n : ℝ) + 1) / 2)) :=
  crossingFactor_eq_gammaForm n hn

-- ============================================================
-- Part VI: Sanity Checks — Recomputing Known Values via the Formula
-- ============================================================

/-- The closed form reproduces α₂ = 2/π. -/
theorem gammaForm_two : gammaForm 2 = 2 / π := by
  rw [← crossingFactor_eq_gammaForm 2 (by norm_num), crossingFactor_two]

/-- The closed form reproduces α₃ = 1/2. -/
theorem gammaForm_three : gammaForm 3 = 1 / 2 := by
  rw [← crossingFactor_eq_gammaForm 3 (by norm_num), crossingFactor_three]

/-- The closed form reproduces α₄ = 4/(3π). -/
theorem gammaForm_four : gammaForm 4 = 4 / (3 * π) := by
  rw [← crossingFactor_eq_gammaForm 4 (by norm_num), crossingFactor_four]

/-- The closed form reproduces α₅ = 3/8. -/
theorem gammaForm_five : gammaForm 5 = 3 / 8 := by
  rw [← crossingFactor_eq_gammaForm 5 (by norm_num), crossingFactor_five]

-- ============================================================
-- Part VII: Buffon Formula in Closed Form
-- ============================================================

/-- The general n-dimensional Buffon expected-crossing formula, with the crossing
    factor given explicitly by Gamma values:

      `E[crossings] = (Γ(n/2) / (√π · Γ((n+1)/2))) · L/d`. -/
theorem buffonNd_closed_form (n : ℕ) (hn : 2 ≤ n) (L d : ℝ) :
    buffonNd n L d =
      (Real.Gamma ((n : ℝ) / 2) / (Real.sqrt π * Real.Gamma (((n : ℝ) + 1) / 2))) * (L / d) := by
  unfold buffonNd
  rw [crossingFactor_closed_form n hn]

end BuffonsNeedleOQ02OQ01OQ01
