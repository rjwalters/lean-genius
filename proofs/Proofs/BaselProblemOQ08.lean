/-
# Basel Problem OQ-08: the value ζ(4) = π⁴/90

## Open Question
Formalize `∑' n, 1 / n⁴ = π⁴ / 90`, the degree-4 analogue of the Basel problem
`∑' n, 1 / n² = π²/6`, by specialising Mathlib's even-zeta formula at argument 4.

## Approach
Mathlib already proves `hasSum_zeta_four : HasSum (fun n => 1/n⁴) (π⁴/90)` (and the
companion `hasSum_zeta_two`) via the Bernoulli/Hurwitz-zeta even-argument formula. This
entry packages the `tsum` value, the `riemannZeta 4` value, and — combining the two
classical even-zeta values — the dimensionless Euler ratio
`ζ(4) / ζ(2)² = 2/5`, which is independent of π.

Sorry-free and axiom-free.
-/
import Mathlib

namespace BaselProblemOQ08

open Real BigOperators

/-- The summable family `n ↦ 1/n⁴` has sum `π⁴/90` (Mathlib's `hasSum_zeta_four`). -/
theorem hasSum_one_div_nat_pow_four :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (π ^ 4 / 90) :=
  hasSum_zeta_four

/-- **ζ(4) = π⁴/90.** The infinite sum `∑' n, 1/n⁴` over the naturals equals `π⁴/90`. -/
theorem tsum_one_div_nat_pow_four :
    ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4 = π ^ 4 / 90 :=
  hasSum_zeta_four.tsum_eq

/-- The Riemann zeta function at `4` equals `π⁴/90` (Mathlib's `riemannZeta_four`). -/
theorem riemannZeta_four_eq : riemannZeta 4 = (π : ℂ) ^ 4 / 90 :=
  riemannZeta_four

/-- **Euler's ratio `ζ(4) / ζ(2)² = 2/5`.** Dividing the two classical even-zeta values
`ζ(4) = π⁴/90` and `ζ(2) = π²/6` makes π cancel, leaving the rational `2/5`. -/
theorem tsum_four_div_tsum_two_sq :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) / (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 2 = 2 / 5 := by
  rw [tsum_one_div_nat_pow_four, hasSum_zeta_two.tsum_eq]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h4 : (π : ℝ) ^ 4 ≠ 0 := pow_ne_zero _ hπ
  field_simp
  ring

end BaselProblemOQ08
