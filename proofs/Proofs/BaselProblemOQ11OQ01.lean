/-
  # The Dirichlet eta / zeta relation at even integers
  # η(2m) = (1 − 2^{1−2m}) ζ(2m)   (basel-problem-oq-11-oq-01)

  ## The open question

  The parent entry `basel-problem-oq-11` proves the single value
  η(2) = ∑ (-1)^(n+1)/n² = π²/12 via the parity split η(2) = (1/2) ζ(2).
  This file *generalizes* that argument once and for all: for **every** exponent
  `e ≥ 1`, knowing the zeta-type sum `∑ 1/n^e = Z` already determines the
  alternating ("eta") sum,

      ∑ (-1)^(n+1)/n^e  =  (1 − 2^{1−e}) · Z.

  Specializing `e = 2m` to an even argument and plugging Mathlib's evaluations of
  ζ(2) and ζ(4) then yields, with **no new analytic input**,

      η(2) = (1 − 1/2)·ζ(2) = (1/2)(π²/6)  = π²/12,
      η(4) = (1 − 1/8)·ζ(4) = (7/8)(π⁴/90) = 7π⁴/720.

  ## The argument (one parity split, exponent-generic)

  Write `Z = ∑_{n≥1} 1/n^e`. Splitting by parity with `HasSum.even_add_odd`:

    * **even part** `∑_k 1/(2k)^e = (1/2^e) Z`, since 1/(2k)^e = (1/2^e)(1/k^e);
    * **odd part**  `∑_k 1/(2k+1)^e = (1 − 1/2^e) Z`, recovered as `Z` minus the
      even part by uniqueness of sums (`HasSum.unique`).

  For the alternating series the even-indexed terms carry sign (-1)^(2k+1) = -1
  and the odd-indexed terms (-1)^(2k+2) = +1, so

      η = −(1/2^e) Z + (1 − 1/2^e) Z = (1 − 2/2^e) Z = (1 − 2^{1−e}) Z.

  Everything is `npow` in a fixed natural exponent `e`, so no `rpow` or analytic
  continuation is needed — only the convergent series identity at the integer point.

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real

namespace BaselEtaEven

/-- The alternating ("eta") summand at exponent `e`: `(-1)^(n+1) / n^e`.
    (At `n = 0` this is `±1/0 = 0` in ℝ, so the series effectively starts at n = 1.) -/
noncomputable def etaSummand (e n : ℕ) : ℝ := (-1) ^ (n + 1) / (n : ℝ) ^ e

/-- **Even-indexed zeta subseries, generic exponent.** From `∑ 1/n^e = Z` the
    even-indexed terms `1/(2k)^e` form a `(1/2^e)`-scaled copy, summing to `(1/2^e)·Z`. -/
theorem hasSum_even_of_hasSum_zeta {e : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ e) Z) :
    HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ e) ((1 / 2 ^ e) * Z) := by
  have hscaled := hZ.mul_left (1 / 2 ^ e : ℝ)
  have hfe : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ e)
      = (fun k : ℕ => (1 / 2 ^ e : ℝ) * (1 / (k : ℝ) ^ e)) := by
    funext k
    have h2k : ((2 * k : ℕ) : ℝ) ^ e = 2 ^ e * (k : ℝ) ^ e := by
      push_cast; rw [mul_pow]
    rw [h2k]
    simp only [one_div, mul_inv]
  rw [hfe]; exact hscaled

/-- **Odd-indexed zeta subseries, generic exponent.** From `∑ 1/n^e = Z` the
    odd-indexed terms sum to `(1 − 1/2^e)·Z`, obtained as `Z` minus the even part
    via `HasSum.even_add_odd` and uniqueness of sums. -/
theorem hasSum_odd_of_hasSum_zeta {e : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ e) Z) :
    HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e) ((1 - 1 / 2 ^ e) * Z) := by
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e) :=
    hZ.summable.comp_injective (fun a b h => by omega)
  have heven := hasSum_even_of_hasSum_zeta hZ
  have hkey : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ e)
      ((1 / 2 ^ e) * Z + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e) :=
    HasSum.even_add_odd heven hodd_summable.hasSum
  have hsum_eq : (1 / 2 ^ e) * Z + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e = Z :=
    hkey.unique hZ
  have hval : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e = (1 - 1 / 2 ^ e) * Z := by
    have hstep : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e = Z - (1 / 2 ^ e) * Z := by linarith
    rw [hstep]; ring
  rw [← hval]; exact hodd_summable.hasSum

/-- **The Dirichlet eta / zeta relation at a natural exponent `e`.**
    From `∑ 1/n^e = Z` we get `∑ (-1)^(n+1)/n^e = (1 − 2/2^e)·Z`, i.e.
    `η(e) = (1 − 2^{1−e}) ζ(e)`. -/
theorem hasSum_eta_of_hasSum_zeta {e : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ e) Z) :
    HasSum (etaSummand e) ((1 - 2 / 2 ^ e) * Z) := by
  -- Even-indexed alternating terms: (-1)^(2k+1)/(2k)^e = -1/(2k)^e, summing to -(1/2^e)Z.
  have ha_even : HasSum (fun k : ℕ => etaSummand e (2 * k)) (-((1 / 2 ^ e) * Z)) := by
    have hfe : (fun k : ℕ => etaSummand e (2 * k))
        = (fun k : ℕ => -(1 / ((2 * k : ℕ) : ℝ) ^ e)) := by
      funext k
      simp only [etaSummand]
      rw [Odd.neg_one_pow (⟨k, by ring⟩ : Odd (2 * k + 1))]
      ring
    rw [hfe]; exact (hasSum_even_of_hasSum_zeta hZ).neg
  -- Odd-indexed alternating terms: (-1)^(2k+2)/(2k+1)^e = 1/(2k+1)^e, summing to (1-1/2^e)Z.
  have ha_odd : HasSum (fun k : ℕ => etaSummand e (2 * k + 1)) ((1 - 1 / 2 ^ e) * Z) := by
    have hfo : (fun k : ℕ => etaSummand e (2 * k + 1))
        = (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ e) := by
      funext k
      simp only [etaSummand]
      rw [Even.neg_one_pow (⟨k + 1, by ring⟩ : Even (2 * k + 1 + 1))]
    rw [hfo]; exact hasSum_odd_of_hasSum_zeta hZ
  have ha : HasSum (etaSummand e) (-((1 / 2 ^ e) * Z) + (1 - 1 / 2 ^ e) * Z) :=
    HasSum.even_add_odd ha_even ha_odd
  have hval : -((1 / 2 ^ e) * Z) + (1 - 1 / 2 ^ e) * Z = (1 - 2 / 2 ^ e) * Z := by ring
  rwa [hval] at ha

/-- **η(2) = π²/12**, recovered from the generic relation at `e = 2` and Mathlib's ζ(2). -/
theorem hasSum_eta_two : HasSum (etaSummand 2) (π ^ 2 / 12) := by
  have h := hasSum_eta_of_hasSum_zeta hasSum_zeta_two
  have hval : (1 - 2 / (2 : ℝ) ^ 2) * (π ^ 2 / 6) = π ^ 2 / 12 := by ring
  rwa [hval] at h

/-- **η(4) = 7π⁴/720**, the new value: the generic relation at `e = 4` applied to
    Mathlib's `hasSum_zeta_four` (ζ(4) = π⁴/90), with no new analytic input. -/
theorem hasSum_eta_four : HasSum (etaSummand 4) (7 * π ^ 4 / 720) := by
  have h := hasSum_eta_of_hasSum_zeta hasSum_zeta_four
  have hval : (1 - 2 / (2 : ℝ) ^ 4) * (π ^ 4 / 90) = 7 * π ^ 4 / 720 := by ring
  rwa [hval] at h

/-- **η(2)** in `tsum` form: `∑' n, (-1)^(n+1)/n² = π²/12`. -/
theorem tsum_eta_two : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 = π ^ 2 / 12 := by
  simpa [etaSummand] using hasSum_eta_two.tsum_eq

/-- **η(4)** in `tsum` form: `∑' n, (-1)^(n+1)/n⁴ = 7π⁴/720`. -/
theorem tsum_eta_four : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 = 7 * π ^ 4 / 720 := by
  simpa [etaSummand] using hasSum_eta_four.tsum_eq

end BaselEtaEven

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_even_of_hasSum_zeta` | ∑_k 1/(2k)^e = (1/2^e)·Z from ζ(e)=Z |
  | `hasSum_odd_of_hasSum_zeta`  | ∑_k 1/(2k+1)^e = (1−1/2^e)·Z from ζ(e)=Z |
  | `hasSum_eta_of_hasSum_zeta`  | ∑ (-1)^(n+1)/n^e = (1−2^{1−e})·Z  (η(e) = (1−2^{1−e})ζ(e)) |
  | `hasSum_eta_two`  | η(2) = π²/12  (e = 2) |
  | `hasSum_eta_four` | η(4) = 7π⁴/720  (e = 4, the new value) |
  | `tsum_eta_two` / `tsum_eta_four` | tsum forms of the two values |

  The parent `basel-problem-oq-11` proved only the `e = 2` instance by hand; here the
  even/odd parity split is carried out once at a generic exponent `e`, so each new
  even value of η is a one-line specialization of `hasSum_eta_of_hasSum_zeta` against
  the corresponding Mathlib ζ evaluation.

  **Sorries**: 0
  **Axioms**: 0
-/
