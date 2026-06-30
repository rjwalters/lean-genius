/-
  # Dirichlet eta value η(4) = ∑_{n≥1} (-1)^(n+1)/n⁴ = 7π⁴/720
  # (basel-problem-oq-13-oq-01)

  ## The Open Question (from basel-problem-oq-13)

  > Derive the Dirichlet eta value η(4) = 7π⁴/720 by combining λ(4) = π⁴/96
  > with the even-fourth-power sum π⁴/1440.

  ## The parity decomposition of η(4)

  The Dirichlet eta function η(s) = ∑_{n≥1} (-1)^(n+1)/nˢ is the alternating
  companion of ζ(s). Splitting the alternating sum by parity, the odd indices
  carry a `+` sign and the even indices a `−` sign:

      η(4) = (∑_{k≥0} 1/(2k+1)⁴) − (∑_{k≥1} 1/(2k)⁴)
           = λ(4) − (even-fourth-power sum)
           = π⁴/96 − π⁴/1440
           = (15π⁴ − π⁴)/1440 = 14π⁴/1440 = 7π⁴/720.

  Both ingredients are already proved (axiom-free) in the parent file
  `BaselProblemOQ13`:

    * `hasSum_even_zeta_four` : ∑_k 1/(2k)⁴ = π⁴/1440,
    * `hasSum_odd_zeta_four`  : ∑_k 1/(2k+1)⁴ = π⁴/96.

  The only new ingredient here is the *alternating* sign, threaded through
  `HasSum.even_add_odd`: with f n = (-1)^(n+1)/n⁴ we have f(2k) = -1/(2k)⁴ and
  f(2k+1) = +1/(2k+1)⁴, so η(4) = (−even part) + (odd part). No new analytic
  input.

  ## Axiom count: 0
-/

import Proofs.BaselProblemOQ13
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real

namespace BaselEtaFour

open BaselOddZetaFour

/-- The even-indexed terms of η(4): with the alternating sign, `f(2k) = -1/(2k)⁴`,
    summing to `-π⁴/1440` (the negative of the even-fourth-power sum). -/
theorem hasSum_eta_four_even :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4)
      (-(π ^ 4 / 1440)) := by
  have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4)
      = (fun k : ℕ => -(1 / ((2 * k : ℕ) : ℝ) ^ 4)) := by
    funext k
    have hsign : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    rw [hsign]; ring
  rw [hfun]
  exact hasSum_even_zeta_four.neg

/-- The odd-indexed terms of η(4): with the alternating sign, `f(2k+1) = +1/(2k+1)⁴`,
    summing to `π⁴/96` (the odd-fourth-power / lambda value λ(4)). -/
theorem hasSum_eta_four_odd :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
      (π ^ 4 / 96) := by
  have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
      = (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) := by
    funext k
    have hsign : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
      rw [pow_succ, pow_succ, pow_mul]; norm_num
    rw [hsign]
  rw [hfun]
  exact hasSum_odd_zeta_four

/-- **Dirichlet eta value η(4)** as a `HasSum`:
    `∑_{n} (-1)^(n+1)/n⁴ = 7π⁴/720`.

    Assembled from the parent's even/odd fourth-power sums via the parity split
    `HasSum.even_add_odd`: η(4) = (−π⁴/1440) + π⁴/96 = 7π⁴/720. The `n = 0` term
    is `(-1)^1 / 0^4 = 0` (division by zero), so it contributes nothing. -/
theorem hasSum_eta_four :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4) (7 * π ^ 4 / 720) := by
  have h := HasSum.even_add_odd
    (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4)
    hasSum_eta_four_even hasSum_eta_four_odd
  convert h using 1
  ring

/-- **Dirichlet eta value η(4)** in `tsum` form: `∑' n, (-1)^(n+1)/n⁴ = 7π⁴/720`. -/
theorem tsum_eta_four :
    ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 = 7 * π ^ 4 / 720 :=
  hasSum_eta_four.tsum_eq

end BaselEtaFour

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_eta_four_even` | ∑ (-1)^(2k+1)/(2k)⁴ = -π⁴/1440 |
  | `hasSum_eta_four_odd`  | ∑ (-1)^(2k+2)/(2k+1)⁴ = π⁴/96 |
  | `hasSum_eta_four`      | ∑ (-1)^(n+1)/n⁴ = 7π⁴/720 (HasSum) |
  | `tsum_eta_four`        | ∑' n, (-1)^(n+1)/n⁴ = 7π⁴/720 |

  Built entirely from the parent `BaselProblemOQ13`'s even/odd fourth-power sums
  (`hasSum_even_zeta_four`, `hasSum_odd_zeta_four`) and the parity split
  `HasSum.even_add_odd`.

  **Sorries**: 0
  **Axioms**: 0
-/
