/-
The Wallis Product as a Standalone Limit:  ∏ 4k²/(4k²−1) → π/2

Source: Open question from stirling-formula gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

The gallery's Stirling entries (`StirlingFormula`, `StirlingExpansion`, …) use the
Wallis product *internally* as the engine that pins the Stirling constant to √(2π),
but none of them states Wallis' product in its own classical textbook form. This
file isolates it:

  ∏_{k=1}^{n}  (2k)² / ((2k−1)(2k+1))  =  ∏_{k=1}^{n} 4k²/(4k²−1)  ⟶  π/2.

This is John Wallis' 1656 infinite product for π (from *Arithmetica Infinitorum*),
the historical ancestor of the Stirling-constant computation. Mathlib proves the
limit in a shifted, index-from-zero form (`Real.tendsto_prod_pi_div_two`); we
reindex it to the standard k-from-1 factor 4k²/(4k²−1) and record the algebraic
identity that the two factor forms coincide.

We prove:
1. `wallis_factor`     — the textbook identity 4k²/(4k²−1) = (2k)²/((2k−1)(2k+1))
2. `wallisProduct_eq`  — our product equals Mathlib's shifted Wallis product termwise
3. `wallis_tendsto`    — the standalone limit ∏ 4k²/(4k²−1) → π/2
-/

import Mathlib

open Finset Filter Topology Real

namespace StirlingFormulaOQ03

/-- The `n`-th partial Wallis product in classical form:
`∏_{k=1}^{n} 4k²/(4k²−1)`, indexed with `k = i+1` over `range n`. -/
noncomputable def wallisProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (4 * ((i : ℝ) + 1) ^ 2) / (4 * ((i : ℝ) + 1) ^ 2 - 1)

/-! ## Part I: The factor identity -/

/-- The Wallis factor in its two standard forms agree:
`4k²/(4k²−1) = (2k)²/((2k−1)(2k+1))`. The denominator factors as a difference of
squares: `4k² − 1 = (2k−1)(2k+1)`. -/
theorem wallis_factor (k : ℝ) :
    4 * k ^ 2 / (4 * k ^ 2 - 1) = (2 * k) ^ 2 / ((2 * k - 1) * (2 * k + 1)) := by
  have hd : 4 * k ^ 2 - 1 = (2 * k - 1) * (2 * k + 1) := by ring
  rw [hd]
  ring

/-! ## Part II: Reindexing to Mathlib's shifted product -/

/-- Termwise, our classical product matches Mathlib's index-from-zero Wallis
product `(2i+2)/(2i+1) · (2i+2)/(2i+3)` (with `i = k−1`). -/
theorem wallisProduct_eq (n : ℕ) :
    wallisProduct n
      = ∏ i ∈ Finset.range n,
          ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)) := by
  unfold wallisProduct
  apply Finset.prod_congr rfl
  intro i _
  have h1 : (2 : ℝ) * i + 1 ≠ 0 := by positivity
  have h2 : (2 : ℝ) * i + 3 ≠ 0 := by positivity
  have h3 : 4 * ((i : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
    have : 4 * ((i : ℝ) + 1) ^ 2 - 1 = (2 * i + 1) * (2 * i + 3) := by ring
    rw [this]; positivity
  field_simp
  ring

/-! ## Part III: The standalone Wallis limit -/

/-- **Wallis' product (1656).** The classical partial products converge to `π/2`:

  `∏_{k=1}^{n} 4k²/(4k²−1) ⟶ π/2`.

Obtained by reindexing Mathlib's `Real.tendsto_prod_pi_div_two`. -/
theorem wallis_tendsto :
    Tendsto wallisProduct atTop (𝓝 (π / 2)) :=
  Real.tendsto_prod_pi_div_two.congr (fun n => (wallisProduct_eq n).symm)

end StirlingFormulaOQ03
