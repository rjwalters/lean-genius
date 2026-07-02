/-
# Alternating-Series Boole Summation — OQ-03
## Exact closed form for the alternating sum of a quadratic sequence

The parent entry `AlternatingSeriesBooleSummation.lean` builds the exact finite Boole
summation engine and, as its terminal application, proves the closed form `altSum_affine`
for the alternating sum of an *affine* sequence `a_j = α + β·j`: the order-`2` Boole formula
terminates because `Δ²(α+βj) ≡ 0`, so the alternating sum is a pure endpoint expression.

This file climbs the next rung of the polynomial ladder — a *quadratic* sequence
`a_j = α + β·j + γ·j²`.  Its forward differences are

  `Δa_j  = (β+γ) + 2γ·j`   (affine),
  `Δ²a_j = 2γ`             (constant),
  `Δ³a_j = 0`,

so the order-`3` Boole formula `boole_exact_of_iterate_fdiff_zero` terminates and evaluates
completely, giving the alternating sum as a pure endpoint expression with no remainder:

  `∑_{j=n}^{m-1} (-1)^j (α + βj + γj²)`
  `  = ½·((-1)^n (α+βn+γn²) - (-1)^m (α+βm+γm²))`
  `    - ¼·((-1)^n ((β+γ)+2γn) - (-1)^m ((β+γ)+2γm))`
  `    + ¼·γ·((-1)^n - (-1)^m)`.

Everything reuses the verified parent engine (`fdiff`, `altSum`, `fdiff_affine`,
`iterate_fdiff_two_affine`, `boole_exact_of_iterate_fdiff_zero`); the file is axiom-free
over `ℝ`.

**Category**: application / specialization of the parent's finite Boole engine.
-/

import Mathlib.Tactic
import Proofs.AlternatingSeriesBooleSummation

namespace AlternatingSeriesBooleSummationOQ03

open AlternatingSeriesBooleSummation

/-- The forward difference of a quadratic `a_j = α + β·j + γ·j²` is the affine sequence
`(β+γ) + 2γ·j`: the discrete analogue of `(α+βx+γx²)' = β+2γx`, with the `γ·(2j+1)` shape of
the finite difference regrouped as `(β+γ) + 2γ·j`. -/
theorem fdiff_quadratic (α β γ : ℝ) :
    fdiff (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)
      = fun (j : ℕ) => (β + γ) + 2 * γ * (j : ℝ) := by
  funext j; simp only [fdiff]; push_cast; ring

/-- The second forward difference of a quadratic is the constant `2γ`.  Reuses the parent's
`fdiff_affine` applied to the affine first difference. -/
theorem fdiff_two_quadratic (α β γ : ℝ) :
    fdiff^[2] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2) = fun _ => 2 * γ := by
  have h1 : fdiff^[2] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)
      = fdiff (fdiff^[1] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)) :=
    congrFun (Function.iterate_succ' fdiff 1) _
  rw [h1, Function.iterate_one, fdiff_quadratic]
  exact fdiff_affine (β + γ) (2 * γ)

/-- The third forward difference of a quadratic vanishes identically — `Δ³` kills degree `≤ 2`,
so the order-`3` Boole remainder is exactly zero. -/
theorem iterate_fdiff_three_quadratic (α β γ : ℝ) :
    ∀ j, (fdiff^[3] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)) j = 0 := by
  have h1 : fdiff^[3] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)
      = fdiff (fdiff^[2] (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2)) :=
    congrFun (Function.iterate_succ' fdiff 2) _
  rw [h1, fdiff_two_quadratic]
  intro j
  simp only [fdiff, sub_self]

/-- **Exact closed form for the alternating sum of a quadratic sequence.** Since
`Δ³(α + β·j + γ·j²) ≡ 0`, the order-`3` Boole formula terminates and evaluates completely: the
alternating sum of a quadratic progression is a pure endpoint expression, with no remainder.

`∑_{j=n}^{m-1} (-1)^j (α + βj + γj²)`
`  = ½·((-1)^n (α+βn+γn²) - (-1)^m (α+βm+γm²))`
`    - ¼·((-1)^n ((β+γ)+2γn) - (-1)^m ((β+γ)+2γm))`
`    + ¼·γ·((-1)^n - (-1)^m)`.

This is the degree-`2` rung of the polynomial ladder whose degree-`0` (`altSum_const`) and
degree-`1` (`altSum_affine`) rungs are proved in the parent. -/
theorem altSum_quadratic (α β γ : ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2) n m
      = (1 / 2) * ((-1 : ℝ) ^ n * (α + β * (n : ℝ) + γ * (n : ℝ) ^ 2)
            - (-1 : ℝ) ^ m * (α + β * (m : ℝ) + γ * (m : ℝ) ^ 2))
        - (1 / 4) * ((-1 : ℝ) ^ n * ((β + γ) + 2 * γ * (n : ℝ))
            - (-1 : ℝ) ^ m * ((β + γ) + 2 * γ * (m : ℝ)))
        + (1 / 4) * γ * ((-1 : ℝ) ^ n - (-1 : ℝ) ^ m) := by
  rw [boole_exact_of_iterate_fdiff_zero (fun j => α + β * (j : ℝ) + γ * (j : ℝ) ^ 2) n m h 3
        (iterate_fdiff_three_quadratic α β γ),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Function.iterate_zero, id_eq, pow_zero, pow_one, Function.iterate_one,
    fdiff_quadratic, fdiff_two_quadratic]
  push_cast
  ring

/-- **Closed form for the pure alternating sum of squares** `∑_{j=n}^{m-1} (-1)^j j²`, the
`α = β = 0`, `γ = 1` specialization of `altSum_quadratic`. -/
theorem altSum_sq (n m : ℕ) (h : n ≤ m) :
    altSum (fun j => (j : ℝ) ^ 2) n m
      = (1 / 2) * ((-1 : ℝ) ^ n * (n : ℝ) ^ 2 - (-1 : ℝ) ^ m * (m : ℝ) ^ 2)
        - (1 / 4) * ((-1 : ℝ) ^ n * (1 + 2 * (n : ℝ)) - (-1 : ℝ) ^ m * (1 + 2 * (m : ℝ)))
        + (1 / 4) * ((-1 : ℝ) ^ n - (-1 : ℝ) ^ m) := by
  have key : (fun j : ℕ => (j : ℝ) ^ 2)
      = (fun j : ℕ => (0 : ℝ) + 0 * (j : ℝ) + 1 * (j : ℝ) ^ 2) := by funext j; ring
  rw [key, altSum_quadratic 0 0 1 n m h]; ring

end AlternatingSeriesBooleSummationOQ03
