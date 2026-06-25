/-
The Catalan Number Asymptotic:  catalan n · n · √(πn) / 4ⁿ → 1,  i.e.  Cₙ ~ 4ⁿ / (√π · n^{3/2})

Source: Open question from stirling-formula-oq-03-oq-02 (the central binomial asymptotic)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry `StirlingFormulaOQ03OQ02` establishes the asymptotics of the central
binomial coefficient,

  **`centralBinom_asymptotic`**:  `C(2n,n) · √(πn) / 4ⁿ → 1`,   i.e.  `C(2n,n) ~ 4ⁿ/√(πn)`.

This file derives the corresponding asymptotic for the **Catalan numbers**
`Cₙ = catalan n`.  The bridge is the exact Mathlib identity

  `(n+1) · catalan n = C(2n,n)`   (`Nat.succ_mul_catalan_eq_centralBinom`),

equivalently `catalan n = C(2n,n)/(n+1)`.  Multiplying the parent limit by the elementary
ratio `n/(n+1) → 1` and folding the cast identity in gives

  **`catalan_asymptotic`**:  `catalan n · n · √(πn) / 4ⁿ → 1`.

Since `n · √(πn) = √π · n^{3/2}`, this is exactly the textbook statement

  `Cₙ ~ 4ⁿ / (√π · n^{3/2})`.

We also record the equivalent reciprocal form `4ⁿ / (catalan n · n · √(πn)) → 1`.

## Relation to Mathlib

Mathlib has the exact relation between the Catalan number and the central binomial
coefficient (`Nat.succ_mul_catalan_eq_centralBinom`, `Nat.catalan_eq_centralBinom_div`) and
the central binomial/Wallis machinery, but it does **not** state the *asymptotic* growth of
the Catalan numbers. We assemble it from the parent's `centralBinom_asymptotic` and the
elementary limit `n/(n+1) → 1`.
-/

import Mathlib
import Proofs.StirlingFormulaOQ03OQ02

open Filter Topology Nat
open scoped Real

namespace StirlingFormulaOQ03OQ02OQ01

open StirlingFormulaOQ03OQ02 (cb cb_pos cb_ne_zero centralBinom_asymptotic)

/-- Real-valued Catalan number, for convenience. -/
noncomputable def cat (n : ℕ) : ℝ := (catalan n : ℝ)

/-- The Catalan numbers are positive (follows from `(n+1)·catalan n = C(2n,n) > 0`). -/
theorem cat_pos (n : ℕ) : 0 < cat n := by
  have hpos : 0 < catalan n := by
    rcases Nat.eq_zero_or_pos (catalan n) with h | h
    · exfalso
      have hid := succ_mul_catalan_eq_centralBinom n
      rw [h, Nat.mul_zero] at hid
      exact (Nat.centralBinom_pos n).ne' hid.symm
    · exact h
  unfold cat; exact_mod_cast hpos

theorem cat_ne_zero (n : ℕ) : cat n ≠ 0 := (cat_pos n).ne'

/-! ## Part I: The exact bridge to the central binomial coefficient -/

/-- `catalan n = C(2n,n)/(n+1)`, cast to `ℝ`. -/
theorem cat_eq (n : ℕ) : cat n = cb n / (n + 1) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hne]
  unfold cat cb
  have hc := congrArg (Nat.cast (R := ℝ)) (succ_mul_catalan_eq_centralBinom n)
  push_cast at hc
  linear_combination hc

/-! ## Part II: The asymptotics -/

/-- The elementary ratio `n/(n+1) → 1`. -/
theorem ratio_tendsto : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := htop.inv_tendsto_atTop
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with n _
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **Catalan number asymptotic.** `catalan n · n · √(πn) / 4ⁿ → 1`, i.e.
`Cₙ ~ 4ⁿ / (√π · n^{3/2})` (using `n · √(πn) = √π · n^{3/2}`). -/
theorem catalan_asymptotic :
    Tendsto (fun n : ℕ => cat n * n * Real.sqrt (π * n) / (4 : ℝ) ^ n) atTop (𝓝 1) := by
  have hprod := centralBinom_asymptotic.mul ratio_tendsto
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n _
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hcb := cb_ne_zero n
  rw [cat_eq]
  field_simp

/-- Equivalent reciprocal form: `4ⁿ / (catalan n · n · √(πn)) → 1`. -/
theorem catalan_asymptotic_inv :
    Tendsto (fun n : ℕ => (4 : ℝ) ^ n / (cat n * n * Real.sqrt (π * n))) atTop (𝓝 1) := by
  have h := catalan_asymptotic.inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr ?_
  intro n
  rw [inv_div]

end StirlingFormulaOQ03OQ02OQ01
