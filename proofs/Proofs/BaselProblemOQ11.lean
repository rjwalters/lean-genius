/-
  # Dirichlet eta at 2: η(2) = ∑ (-1)^(n+1)/n² = π²/12
  # (basel-problem-oq-11)

  ## The Open Question

  Mathlib's `hasSum_zeta_two` gives the Basel sum ζ(2) = ∑ 1/n² = π²/6. This file
  formalizes the *alternating* companion — the **Dirichlet eta value**

      η(2) = ∑_{n≥1} (-1)^(n+1) / n²  =  π²/12.

  ## The parity split η(2) = (1/2) ζ(2)

  Classically η(s) = (1 - 2^(1-s)) ζ(s); for s = 2 this is η(2) = (1/2) ζ(2) = π²/12.
  The proof here splits the series into even- and odd-indexed parts via Mathlib's
  `HasSum.even_add_odd`:

    * even part:  ∑_k (-1)^(2k+1)/(2k)² = -∑_k 1/(2k)² = -(1/4) ζ(2) = -π²/24,
    * odd part:   ∑_k (-1)^(2k+2)/(2k+1)² = ∑_k 1/(2k+1)² = π²/8,

  and -π²/24 + π²/8 = π²/12. The odd-square sum π²/8 is itself obtained from
  `hasSum_zeta_two` by the same even/odd split: ζ(2) = (even) + (odd) with the even
  part π²/24 forces the odd part to be π²/6 - π²/24 = π²/8.

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real

namespace BaselEtaTwo

/-- The summand of the Dirichlet eta value η(2): `(-1)^(n+1) / n²`.
    (At `n = 0` this is `-1/0 = 0` in ℝ, so the series starts effectively at n = 1.) -/
noncomputable def etaSummand (n : ℕ) : ℝ := (-1) ^ (n + 1) / (n : ℝ) ^ 2

/-- Even-indexed Basel sum: `∑_k 1/(2k)² = π²/24` (a quarter of ζ(2)). -/
theorem hasSum_even_zeta_two :
    HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 24) := by
  have h4 := hasSum_zeta_two.mul_left (1 / 4 : ℝ)
  have hfe : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2)
      = (fun k : ℕ => (1 / 4 : ℝ) * (1 / (k : ℝ) ^ 2)) := by
    funext k; push_cast; ring
  rw [hfe]
  convert h4 using 1
  ring

/-- Odd-indexed Basel sum: `∑_k 1/(2k+1)² = π²/8`. Derived from `hasSum_zeta_two`
    by the even/odd split: ζ(2) = (even part π²/24) + (odd part), so the odd part
    is π²/6 - π²/24 = π²/8. -/
theorem hasSum_odd_zeta_two :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 8) := by
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) :=
    hasSum_zeta_two.summable.comp_injective (fun a b h => by omega)
  -- Reassemble ζ(2) from its even and odd parts.
  have hkey : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2)
      (π ^ 2 / 24 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
    refine HasSum.even_add_odd ?_ ?_
    · exact hasSum_even_zeta_two
    · exact hodd_summable.hasSum
  have hsum_eq : π ^ 2 / 24 + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 6 :=
    hkey.unique hasSum_zeta_two
  have hval : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2 = π ^ 2 / 8 := by linarith
  rw [← hval]
  exact hodd_summable.hasSum

/-- **Dirichlet eta value η(2)**: `∑ (-1)^(n+1)/n² = π²/12`, as a `HasSum`. -/
theorem hasSum_eta_two : HasSum etaSummand (π ^ 2 / 12) := by
  -- Even-indexed part: (-1)^(2k+1)/(2k)² = -1/(2k)², summing to -π²/24.
  have ha_even : HasSum (fun k : ℕ => etaSummand (2 * k)) (-(π ^ 2 / 24)) := by
    have hfe : (fun k : ℕ => etaSummand (2 * k))
        = (fun k : ℕ => -(1 / ((2 * k : ℕ) : ℝ) ^ 2)) := by
      funext k
      simp only [etaSummand]
      rw [Odd.neg_one_pow (⟨k, by ring⟩ : Odd (2 * k + 1))]
      ring
    rw [hfe]; exact hasSum_even_zeta_two.neg
  -- Odd-indexed part: (-1)^(2k+2)/(2k+1)² = 1/(2k+1)², summing to π²/8.
  have ha_odd : HasSum (fun k : ℕ => etaSummand (2 * k + 1)) (π ^ 2 / 8) := by
    have hfo : (fun k : ℕ => etaSummand (2 * k + 1))
        = (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
      funext k
      simp only [etaSummand]
      rw [Even.neg_one_pow (⟨k + 1, by ring⟩ : Even (2 * k + 1 + 1))]
    rw [hfo]; exact hasSum_odd_zeta_two
  have ha : HasSum etaSummand (-(π ^ 2 / 24) + π ^ 2 / 8) :=
    HasSum.even_add_odd ha_even ha_odd
  have hval : -(π ^ 2 / 24) + π ^ 2 / 8 = π ^ 2 / 12 := by ring
  rwa [hval] at ha

/-- **Dirichlet eta value η(2)** in `tsum` form: `∑' n, (-1)^(n+1)/n² = π²/12`. -/
theorem tsum_eta_two : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 = π ^ 2 / 12 :=
  hasSum_eta_two.tsum_eq

end BaselEtaTwo

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_even_zeta_two` | ∑ 1/(2k)² = π²/24 |
  | `hasSum_odd_zeta_two`  | ∑ 1/(2k+1)² = π²/8 |
  | `hasSum_eta_two`       | ∑ (-1)^(n+1)/n² = π²/12 (HasSum) |
  | `tsum_eta_two`         | ∑' n, (-1)^(n+1)/n² = π²/12 |

  Built entirely from Mathlib's `hasSum_zeta_two` (ζ(2) = π²/6) and the even/odd
  series split `HasSum.even_add_odd`.

  **Sorries**: 0
  **Axioms**: 0
-/
