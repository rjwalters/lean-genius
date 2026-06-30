/-
  # Odd-fourth-power zeta sum: ∑_{k≥0} 1/(2k+1)⁴ = π⁴/96
  # (basel-problem-oq-13)

  ## The Open Question

  Mathlib's `hasSum_zeta_four` gives the fourth zeta value ζ(4) = ∑ 1/n⁴ = π⁴/90.
  This file formalizes its **odd-indexed companion**, the *lambda value* λ(4):

      ∑_{k≥0} 1/(2k+1)⁴  =  π⁴/96.

  ## The parity split λ(4) = (1 - 1/16) ζ(4)

  Classically λ(s) = ∑_{k≥0} 1/(2k+1)ˢ = (1 - 2^(-s)) ζ(s); for s = 4 this is
  λ(4) = (1 - 1/16) ζ(4) = (15/16)(π⁴/90) = π⁴/96. The proof splits ζ(4) into its
  even- and odd-indexed parts via Mathlib's `HasSum.even_add_odd`:

    * even part:  ∑_k 1/(2k)⁴ = (1/16) ζ(4) = π⁴/1440,
    * odd part:   ∑_k 1/(2k+1)⁴ = ζ(4) - π⁴/1440 = π⁴/90 - π⁴/1440 = π⁴/96.

  Everything is built from `hasSum_zeta_four` (ζ(4) = π⁴/90) and the even/odd series
  split — no new analytic input.

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real

namespace BaselOddZetaFour

/-- Even-indexed fourth-power sum: `∑_k 1/(2k)⁴ = π⁴/1440` (a sixteenth of ζ(4)). -/
theorem hasSum_even_zeta_four :
    HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 4) (π ^ 4 / 1440) := by
  have h16 := hasSum_zeta_four.mul_left (1 / 16 : ℝ)
  have hfe : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 4)
      = (fun k : ℕ => (1 / 16 : ℝ) * (1 / (k : ℝ) ^ 4)) := by
    funext k; push_cast; ring
  rw [hfe]
  convert h16 using 1
  ring

/-- **Odd-fourth-power zeta sum**: `∑_k 1/(2k+1)⁴ = π⁴/96`. Derived from
    `hasSum_zeta_four` by the even/odd split: ζ(4) = (even part π⁴/1440) + (odd part),
    so the odd part is π⁴/90 - π⁴/1440 = π⁴/96. -/
theorem hasSum_odd_zeta_four :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) (π ^ 4 / 96) := by
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) :=
    hasSum_zeta_four.summable.comp_injective (fun a b h => by omega)
  -- Reassemble ζ(4) from its even and odd parts.
  have hkey : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 4)
      (π ^ 4 / 1440 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) := by
    refine HasSum.even_add_odd ?_ ?_
    · exact hasSum_even_zeta_four
    · exact hodd_summable.hasSum
  have hsum_eq : π ^ 4 / 1440 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4 = π ^ 4 / 90 :=
    hkey.unique hasSum_zeta_four
  have hval : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4 = π ^ 4 / 96 := by linarith
  rw [← hval]
  exact hodd_summable.hasSum

/-- **Odd-fourth-power zeta sum** in `tsum` form: `∑' k, 1/(2k+1)⁴ = π⁴/96`. -/
theorem tsum_odd_zeta_four :
    ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4 = π ^ 4 / 96 :=
  hasSum_odd_zeta_four.tsum_eq

end BaselOddZetaFour

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_even_zeta_four` | ∑ 1/(2k)⁴ = π⁴/1440 |
  | `hasSum_odd_zeta_four`  | ∑ 1/(2k+1)⁴ = π⁴/96 (HasSum) |
  | `tsum_odd_zeta_four`    | ∑' k, 1/(2k+1)⁴ = π⁴/96 |

  Built entirely from Mathlib's `hasSum_zeta_four` (ζ(4) = π⁴/90) and the even/odd
  series split `HasSum.even_add_odd`.

  **Sorries**: 0
  **Axioms**: 0
-/
