import Proofs.CramersRuleOQ04OQ01OQ01
import Mathlib.Tactic

/-
# Cramer's rule OQ-04 → OQ-01 → OQ-01 → OQ-01: the 2×2 and 3×3 closed forms

The parent `CramersRuleOQ04OQ01OQ01` proves the explicit Cramer solution
`xᵢ = det(Aᵢ) / det A` over a field with `det A ≠ 0`, where `Aᵢ = A.updateCol i b`
is `A` with its `i`-th column replaced by the right-hand side `b`. Its open
question OQ-01 asks to

> *Specialize the formula to the 2×2 and 3×3 cases, recovering the elementary
> closed forms (e.g. `x = (b₁a₂₂ − b₂a₁₂)/det A`) and verifying them against
> `det_fin_two` / `det_fin_three`.*

This file does exactly that. The work is purely the bookkeeping of column
replacement: substituting `det_fin_two` / `det_fin_three` into both the parent's
numerator `det(Aᵢ)` and denominator `det A` and resolving the `updateCol`
entries via `Matrix.updateCol_self` (the replaced column equals `b`) and
`Matrix.updateCol_ne` (every other column is untouched). The result is the
textbook quotient-of-determinants formula with the determinants fully expanded
into the entries of `A` and `b`.

## Main results

* `det_updateCol_two_zero`, `det_updateCol_two_one` — the 2×2 numerator
  determinants `det(Aᵢ)` written out in entries.
* `cramer_two_zero`, `cramer_two_one` — the 2×2 closed forms
  `x₀ = (b₀a₁₁ − a₀₁b₁) / (a₀₀a₁₁ − a₀₁a₁₀)`, etc.
* `det_updateCol_three_zero/one/two` — the 3×3 numerator determinants.
* `cramer_three_zero/one/two` — the 3×3 closed forms (Sarrus-expanded).

`0` axioms, `0` sorries.  Everything reduces to the parent `cramer_solution`
together with `det_fin_two` / `det_fin_three`.
-/

namespace CramersRuleOQ04OQ01OQ01OQ01

open Matrix
open CramersRuleOQ04OQ01OQ01

/-! ## The 2×2 case -/

section TwoByTwo

variable {K : Type*} [Field K]

/-- Numerator determinant for the first unknown: replacing column `0` of a 2×2
    matrix `A` by `b` gives `det = b₀·a₁₁ − a₀₁·b₁`. -/
theorem det_updateCol_two_zero (A : Matrix (Fin 2) (Fin 2) K) (b : Fin 2 → K) :
    (A.updateCol 0 b).det = b 0 * A 1 1 - A 0 1 * b 1 := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [det_fin_two]
  simp only [updateCol_self, updateCol_ne h10]

/-- Numerator determinant for the second unknown: replacing column `1` of a 2×2
    matrix `A` by `b` gives `det = a₀₀·b₁ − b₀·a₁₀`. -/
theorem det_updateCol_two_one (A : Matrix (Fin 2) (Fin 2) K) (b : Fin 2 → K) :
    (A.updateCol 1 b).det = A 0 0 * b 1 - b 0 * A 1 0 := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  rw [det_fin_two]
  simp only [updateCol_self, updateCol_ne h01]

/-- **2×2 Cramer's rule, first unknown.** If `A x = b` and `det A ≠ 0` then
    `x₀ = (b₀a₁₁ − a₀₁b₁) / (a₀₀a₁₁ − a₀₁a₁₀)`. -/
theorem cramer_two_zero (A : Matrix (Fin 2) (Fin 2) K) (x b : Fin 2 → K)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x 0 = (b 0 * A 1 1 - A 0 1 * b 1) / (A 0 0 * A 1 1 - A 0 1 * A 1 0) := by
  rw [cramer_solution A x b 0 hx hdet, det_updateCol_two_zero, det_fin_two]

/-- **2×2 Cramer's rule, second unknown.** If `A x = b` and `det A ≠ 0` then
    `x₁ = (a₀₀b₁ − b₀a₁₀) / (a₀₀a₁₁ − a₀₁a₁₀)`. -/
theorem cramer_two_one (A : Matrix (Fin 2) (Fin 2) K) (x b : Fin 2 → K)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x 1 = (A 0 0 * b 1 - b 0 * A 1 0) / (A 0 0 * A 1 1 - A 0 1 * A 1 0) := by
  rw [cramer_solution A x b 1 hx hdet, det_updateCol_two_one, det_fin_two]

end TwoByTwo

/-! ## The 3×3 case -/

section ThreeByThree

variable {K : Type*} [Field K]

/-- Numerator determinant for `x₀`: column `0` of a 3×3 matrix replaced by `b`. -/
theorem det_updateCol_three_zero (A : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K) :
    (A.updateCol 0 b).det =
      b 0 * A 1 1 * A 2 2 - b 0 * A 1 2 * A 2 1
      - A 0 1 * b 1 * A 2 2 + A 0 1 * A 1 2 * b 2
      + A 0 2 * b 1 * A 2 1 - A 0 2 * A 1 1 * b 2 := by
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  rw [det_fin_three]
  simp only [updateCol_self, updateCol_ne h10, updateCol_ne h20]

/-- Numerator determinant for `x₁`: column `1` of a 3×3 matrix replaced by `b`. -/
theorem det_updateCol_three_one (A : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K) :
    (A.updateCol 1 b).det =
      A 0 0 * b 1 * A 2 2 - A 0 0 * A 1 2 * b 2
      - b 0 * A 1 0 * A 2 2 + b 0 * A 1 2 * A 2 0
      + A 0 2 * A 1 0 * b 2 - A 0 2 * b 1 * A 2 0 := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  rw [det_fin_three]
  simp only [updateCol_self, updateCol_ne h01, updateCol_ne h21]

/-- Numerator determinant for `x₂`: column `2` of a 3×3 matrix replaced by `b`. -/
theorem det_updateCol_three_two (A : Matrix (Fin 3) (Fin 3) K) (b : Fin 3 → K) :
    (A.updateCol 2 b).det =
      A 0 0 * A 1 1 * b 2 - A 0 0 * b 1 * A 2 1
      - A 0 1 * A 1 0 * b 2 + A 0 1 * b 1 * A 2 0
      + b 0 * A 1 0 * A 2 1 - b 0 * A 1 1 * A 2 0 := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  rw [det_fin_three]
  simp only [updateCol_self, updateCol_ne h02, updateCol_ne h12]

/-- **3×3 Cramer's rule, first unknown.** The denominator is `det A` in fully
    Sarrus-expanded form. -/
theorem cramer_three_zero (A : Matrix (Fin 3) (Fin 3) K) (x b : Fin 3 → K)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x 0 =
      (b 0 * A 1 1 * A 2 2 - b 0 * A 1 2 * A 2 1
        - A 0 1 * b 1 * A 2 2 + A 0 1 * A 1 2 * b 2
        + A 0 2 * b 1 * A 2 1 - A 0 2 * A 1 1 * b 2)
      / (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
        - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
        + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
  rw [cramer_solution A x b 0 hx hdet, det_updateCol_three_zero, det_fin_three]

/-- **3×3 Cramer's rule, second unknown.** -/
theorem cramer_three_one (A : Matrix (Fin 3) (Fin 3) K) (x b : Fin 3 → K)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x 1 =
      (A 0 0 * b 1 * A 2 2 - A 0 0 * A 1 2 * b 2
        - b 0 * A 1 0 * A 2 2 + b 0 * A 1 2 * A 2 0
        + A 0 2 * A 1 0 * b 2 - A 0 2 * b 1 * A 2 0)
      / (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
        - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
        + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
  rw [cramer_solution A x b 1 hx hdet, det_updateCol_three_one, det_fin_three]

/-- **3×3 Cramer's rule, third unknown.** -/
theorem cramer_three_two (A : Matrix (Fin 3) (Fin 3) K) (x b : Fin 3 → K)
    (hx : A *ᵥ x = b) (hdet : A.det ≠ 0) :
    x 2 =
      (A 0 0 * A 1 1 * b 2 - A 0 0 * b 1 * A 2 1
        - A 0 1 * A 1 0 * b 2 + A 0 1 * b 1 * A 2 0
        + b 0 * A 1 0 * A 2 1 - b 0 * A 1 1 * A 2 0)
      / (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
        - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
        + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
  rw [cramer_solution A x b 2 hx hdet, det_updateCol_three_two, det_fin_three]

end ThreeByThree

end CramersRuleOQ04OQ01OQ01OQ01
