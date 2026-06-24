/-
# The Catalan Generating Function as a Formal Power Series

This file answers the first open question of `combinations-formula-oq-02`:

  > Prove the generating function `C(x) = (1 − √(1 − 4x)) / (2x)`.

The literal closed form involves a square root, which is not an operation on a
general formal power series ring.  Its rigorous, ring-theoretic content is the
pair of algebraic identities the ordinary generating function

  `C(X) = ∑ₙ catalanₙ · Xⁿ ∈ ℚ⟦X⟧`

satisfies, from which the square-root formula is *derived* by solving a quadratic:

  * `catalan_ogf_functional` — the defining **functional equation**
        `C = 1 + X · C²`,
    the formal-power-series shadow of the Catalan convolution recurrence
    `catalanₙ₊₁ = ∑_{i+j=n} catalanᵢ · catalanⱼ` (Mathlib's `catalan_succ'`);

  * `catalan_ogf_sq` — the **square-root form**
        `(2·X·C − 1)² = 1 − 4·X`.
    Reading this as `(2XC − 1)² = 1 − 4X` and taking the branch with
    `C(0) = catalan 0 = 1` gives `2XC − 1 = −√(1 − 4X)`, i.e.
    `C = (1 − √(1 − 4X)) / (2X)` — exactly the stated closed form, now phrased
    entirely inside `ℚ⟦X⟧` with no square-root operation required.

Mathlib records the Catalan convolution recurrence (`catalan_succ'`) but **not**
the generating-function identity, so the power-series packaging here is original.

Verified: 0 sorries, 0 axioms.
-/
import Mathlib

open PowerSeries Finset

namespace CombinationsFormulaOQ02OQ01

/-- The **ordinary generating function** of the Catalan numbers,
`C(X) = ∑ₙ catalanₙ · Xⁿ`, as a formal power series over `ℚ`. -/
noncomputable def C : PowerSeries ℚ := PowerSeries.mk (fun n => (catalan n : ℚ))

/-- The `n`-th coefficient of `C` is the `n`-th Catalan number. -/
@[simp] theorem coeff_C (n : ℕ) : coeff n C = (catalan n : ℚ) := by
  rw [C, coeff_mk]

/-- **Functional equation of the Catalan generating function:** `C = 1 + X · C²`.

This is the formal-power-series form of the Catalan convolution recurrence
`catalanₙ₊₁ = ∑_{i+j=n} catalanᵢ · catalanⱼ`: comparing the coefficient of `Xⁿ⁺¹`
on each side is exactly that recurrence, while the constant terms agree because
`catalan 0 = 1`. -/
theorem catalan_ogf_functional : C = 1 + PowerSeries.X * C ^ 2 := by
  ext n
  rw [map_add]
  cases n with
  | zero =>
      rw [coeff_zero_X_mul, add_zero, coeff_one, if_pos rfl, coeff_C, catalan_zero,
        Nat.cast_one]
  | succ m =>
      rw [coeff_one, if_neg (Nat.succ_ne_zero m), zero_add, coeff_succ_X_mul, sq,
        coeff_mul, coeff_C]
      simp only [coeff_C]
      rw [catalan_succ']
      push_cast
      rfl

/-- **Square-root form of the Catalan generating function:**
`(2·X·C − 1)² = 1 − 4·X`.

Solving this quadratic for `C` and selecting the branch fixed by
`C(0) = catalan 0 = 1` yields `C = (1 − √(1 − 4X)) / (2X)`, the closed form of the
open question, now stated entirely within `ℚ⟦X⟧`.  It is obtained from the
functional equation `C = 1 + X·C²` by a single algebraic substitution
`X·C² = C − 1`. -/
theorem catalan_ogf_sq :
    (2 * PowerSeries.X * C - 1) ^ 2 = 1 - 4 * PowerSeries.X := by
  have hXC2 : PowerSeries.X * C ^ 2 = C - 1 := by
    have h := catalan_ogf_functional
    linear_combination -h
  linear_combination (4 * PowerSeries.X) * hXC2

end CombinationsFormulaOQ02OQ01
