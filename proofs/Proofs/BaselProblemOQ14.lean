/-
  # Dirichlet eta at 4: η(4) = ∑ (-1)^(n+1)/n⁴ = 7π⁴/720
  # (basel-problem-oq-14)

  ## The Open Question

  Mathlib's `hasSum_zeta_four` gives the fourth zeta value ζ(4) = ∑ 1/n⁴ = π⁴/90.
  This file formalizes the *alternating* companion — the **Dirichlet eta value**

      η(4) = ∑_{n≥1} (-1)^(n+1) / n⁴  =  7π⁴/720.

  ## The parity split η(4) = (1 - 1/8) ζ(4)

  Classically η(s) = (1 - 2^(1-s)) ζ(s); for s = 4 this is η(4) = (1 - 1/8) ζ(4)
  = (7/8)(π⁴/90) = 7π⁴/720. The proof splits the alternating series into even- and
  odd-indexed parts via Mathlib's `HasSum.even_add_odd`:

    * even part:  ∑_k (-1)^(2k+1)/(2k)⁴ = -∑_k 1/(2k)⁴ = -(1/16) ζ(4) = -π⁴/1440,
    * odd part:   ∑_k (-1)^(2k+2)/(2k+1)⁴ = ∑_k 1/(2k+1)⁴ = π⁴/96,

  and -π⁴/1440 + π⁴/96 = 7π⁴/720. The odd-fourth-power sum π⁴/96 is itself obtained
  from `hasSum_zeta_four` by the same even/odd split: ζ(4) = (even) + (odd) with the
  even part π⁴/1440 forcing the odd part to be π⁴/90 - π⁴/1440 = π⁴/96.

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real

namespace BaselEtaFour

/-- The summand of the Dirichlet eta value η(4): `(-1)^(n+1) / n⁴`.
    (At `n = 0` this is `-1/0 = 0` in ℝ, so the series starts effectively at n = 1.) -/
noncomputable def etaSummand (n : ℕ) : ℝ := (-1) ^ (n + 1) / (n : ℝ) ^ 4

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

/-- Odd-indexed fourth-power sum: `∑_k 1/(2k+1)⁴ = π⁴/96`. Derived from
    `hasSum_zeta_four` by the even/odd split: ζ(4) = (even part π⁴/1440) + (odd part),
    so the odd part is π⁴/90 - π⁴/1440 = π⁴/96. -/
theorem hasSum_odd_zeta_four :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) (π ^ 4 / 96) := by
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) :=
    hasSum_zeta_four.summable.comp_injective (fun a b h => by omega)
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

/-- **Dirichlet eta value η(4)**: `∑ (-1)^(n+1)/n⁴ = 7π⁴/720`, as a `HasSum`. -/
theorem hasSum_eta_four : HasSum etaSummand (7 * π ^ 4 / 720) := by
  -- Even-indexed part: (-1)^(2k+1)/(2k)⁴ = -1/(2k)⁴, summing to -π⁴/1440.
  have ha_even : HasSum (fun k : ℕ => etaSummand (2 * k)) (-(π ^ 4 / 1440)) := by
    have hfe : (fun k : ℕ => etaSummand (2 * k))
        = (fun k : ℕ => -(1 / ((2 * k : ℕ) : ℝ) ^ 4)) := by
      funext k
      simp only [etaSummand]
      rw [Odd.neg_one_pow (⟨k, by ring⟩ : Odd (2 * k + 1))]
      ring
    rw [hfe]; exact hasSum_even_zeta_four.neg
  -- Odd-indexed part: (-1)^(2k+2)/(2k+1)⁴ = 1/(2k+1)⁴, summing to π⁴/96.
  have ha_odd : HasSum (fun k : ℕ => etaSummand (2 * k + 1)) (π ^ 4 / 96) := by
    have hfo : (fun k : ℕ => etaSummand (2 * k + 1))
        = (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 4) := by
      funext k
      simp only [etaSummand]
      rw [Even.neg_one_pow (⟨k + 1, by ring⟩ : Even (2 * k + 1 + 1))]
    rw [hfo]; exact hasSum_odd_zeta_four
  have ha : HasSum etaSummand (-(π ^ 4 / 1440) + π ^ 4 / 96) :=
    HasSum.even_add_odd ha_even ha_odd
  have hval : -(π ^ 4 / 1440) + π ^ 4 / 96 = 7 * π ^ 4 / 720 := by ring
  rwa [hval] at ha

/-- **Dirichlet eta value η(4)** in `tsum` form: `∑' n, (-1)^(n+1)/n⁴ = 7π⁴/720`. -/
theorem tsum_eta_four : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 = 7 * π ^ 4 / 720 :=
  hasSum_eta_four.tsum_eq

end BaselEtaFour

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_even_zeta_four` | ∑ 1/(2k)⁴ = π⁴/1440 |
  | `hasSum_odd_zeta_four`  | ∑ 1/(2k+1)⁴ = π⁴/96 |
  | `hasSum_eta_four`       | ∑ (-1)^(n+1)/n⁴ = 7π⁴/720 (HasSum) |
  | `tsum_eta_four`         | ∑' n, (-1)^(n+1)/n⁴ = 7π⁴/720 |

  Built entirely from Mathlib's `hasSum_zeta_four` (ζ(4) = π⁴/90) and the even/odd
  series split `HasSum.even_add_odd`.

  **Sorries**: 0
  **Axioms**: 0
-/
