/-
  # Uniform Dirichlet eta values: η(2m) = (1 − 2^{1−2m}) ζ(2m)
  # (basel-problem-oq-14-oq-01)

  ## The Open Question

  The parent entry `basel-problem-oq-14` proved the single Dirichlet eta value
  η(4) = ∑ (-1)^{n+1}/n⁴ = 7π⁴/720 by an even/odd split of the series. Its open
  question asks to **abstract that parity split into one reusable lemma**

      η(2m) = (1 − 2^{1−2m}) ζ(2m),      ζ(2m) = ∑_{n≥1} 1/n^{2m},

  parameterized over the exponent 2m, so that η(2), η(4), η(6), … all follow
  uniformly from Mathlib's `hasSum_zeta_nat`.

  ## The abstraction

  The relation is a pure series identity, valid for *any* convergent zeta series
  (no closed form for ζ needed). Writing the alternating series via
  `HasSum.even_add_odd`:

    * even part:  ∑_k (-1)^{2k+1}/(2k)^{2m} = −∑_k 1/(2k)^{2m} = −2^{−2m} ζ(2m),
    * odd part:   ∑_k (-1)^{2k+2}/(2k+1)^{2m} = ∑_k 1/(2k+1)^{2m}
                  = ζ(2m) − 2^{−2m} ζ(2m)   (the odd half of ζ),

  whose sum is ζ(2m) − 2·2^{−2m} ζ(2m) = (1 − 2^{1−2m}) ζ(2m).

  The master lemma `hasSum_eta_of_zeta` takes an arbitrary `HasSum` witness `Z`
  for the zeta series at exponent `2m` and returns the eta `HasSum`. Feeding it
  `hasSum_zeta_nat` gives the uniform closed form `hasSum_eta_nat`; specialising
  to `m = 1, 2` recovers η(2) = π²/12 (new) and η(4) = 7π⁴/720 (the parent).

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real

namespace BaselEtaZeta

/-- The summand of the Dirichlet eta value η(2m): `(-1)^(n+1) / n^(2m)`.
    (At `n = 0` this is `±1/0 = 0` in ℝ, so the series starts effectively at n = 1.) -/
noncomputable def etaSummand (m n : ℕ) : ℝ := (-1) ^ (n + 1) / (n : ℝ) ^ (2 * m)

/-- The even-indexed half of the zeta series collapses by the scaling
    `1/(2k)^(2m) = (1/2)^(2m) · 1/k^(2m)`:
    `∑_k 1/(2k)^(2m) = (1/2)^(2m) · ζ(2m)`. -/
theorem hasSum_even_zeta (m : ℕ) (Z : ℝ)
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m)) Z) :
    HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ (2 * m)) ((1 / 2 : ℝ) ^ (2 * m) * Z) := by
  have h := hZ.mul_left ((1 / 2 : ℝ) ^ (2 * m))
  have hfe : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ (2 * m))
      = (fun k : ℕ => (1 / 2 : ℝ) ^ (2 * m) * (1 / (k : ℝ) ^ (2 * m))) := by
    funext k
    rw [show ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) by push_cast; ring, mul_pow, div_pow, one_pow,
      div_mul_div_comm, one_mul]
  rw [hfe]; exact h

/-- **Master parity-split lemma.** For any `HasSum` witness `Z` of the zeta series
    `∑ 1/n^(2m)`, the alternating (Dirichlet eta) series satisfies
    `η(2m) = (1 − 2·(1/2)^(2m)) · Z = (1 − 2^{1−2m}) ζ(2m)`.
    The identity needs no closed form for `Z`. -/
theorem hasSum_eta_of_zeta (m : ℕ) (Z : ℝ)
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m)) Z) :
    HasSum (etaSummand m) ((1 - 2 * (1 / 2 : ℝ) ^ (2 * m)) * Z) := by
  -- Even half of ζ.
  have heven : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ (2 * m)) ((1 / 2 : ℝ) ^ (2 * m) * Z) :=
    hasSum_even_zeta m Z hZ
  -- The odd half is summable (restriction of ζ along an injection).
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ (2 * m)) :=
    hZ.summable.comp_injective (fun a b h => by omega)
  -- ζ = even + odd, so the odd half equals ζ − (even half).
  have hsplit : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * m))
      ((1 / 2 : ℝ) ^ (2 * m) * Z + ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ (2 * m)) :=
    HasSum.even_add_odd heven hodd_summable.hasSum
  have hodd_val : ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ (2 * m) = Z - (1 / 2 : ℝ) ^ (2 * m) * Z := by
    have := hsplit.unique hZ; linarith
  have hodd : HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ (2 * m))
      (Z - (1 / 2 : ℝ) ^ (2 * m) * Z) := by
    rw [← hodd_val]; exact hodd_summable.hasSum
  -- Eta even half: (-1)^(2k+1)/(2k)^(2m) = -1/(2k)^(2m).
  have ha_even : HasSum (fun k : ℕ => etaSummand m (2 * k)) (-((1 / 2 : ℝ) ^ (2 * m) * Z)) := by
    have hfe : (fun k : ℕ => etaSummand m (2 * k))
        = (fun k : ℕ => -(1 / ((2 * k : ℕ) : ℝ) ^ (2 * m))) := by
      funext k
      simp only [etaSummand]
      rw [Odd.neg_one_pow (⟨k, by ring⟩ : Odd (2 * k + 1))]
      ring
    rw [hfe]; exact heven.neg
  -- Eta odd half: (-1)^(2k+2)/(2k+1)^(2m) = 1/(2k+1)^(2m).
  have ha_odd : HasSum (fun k : ℕ => etaSummand m (2 * k + 1)) (Z - (1 / 2 : ℝ) ^ (2 * m) * Z) := by
    have hfo : (fun k : ℕ => etaSummand m (2 * k + 1))
        = (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ (2 * m)) := by
      funext k
      simp only [etaSummand]
      rw [Even.neg_one_pow (⟨k + 1, by ring⟩ : Even (2 * k + 1 + 1))]
    rw [hfo]; exact hodd
  have ha : HasSum (etaSummand m)
      (-((1 / 2 : ℝ) ^ (2 * m) * Z) + (Z - (1 / 2 : ℝ) ^ (2 * m) * Z)) :=
    HasSum.even_add_odd ha_even ha_odd
  have hval : -((1 / 2 : ℝ) ^ (2 * m) * Z) + (Z - (1 / 2 : ℝ) ^ (2 * m) * Z)
      = (1 - 2 * (1 / 2 : ℝ) ^ (2 * m)) * Z := by ring
  rwa [hval] at ha

/-- The eta coefficient in its recognizable form: `1 − 2·(1/2)^(2m) = 1 − 2^{1−2m}`
    (real zpow with the negative integer exponent `1 − 2m`). -/
theorem eta_coeff_eq (m : ℕ) :
    (1 - 2 * (1 / 2 : ℝ) ^ (2 * m)) = 1 - (2 : ℝ) ^ ((1 : ℤ) - 2 * (m : ℤ)) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  congr 1
  rw [show (1 : ℤ) - 2 * (m : ℤ) = 1 - ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ h2,
    zpow_one, zpow_natCast, one_div, inv_pow, div_eq_mul_inv]

/-- **Uniform Dirichlet eta value.** Composing the parity-split lemma with Mathlib's
    `hasSum_zeta_nat` gives, for every `m ≥ 1`,
    `η(2m) = (1 − 2^{1−2m}) ζ(2m)` with `ζ(2m) = ∑ 1/n^(2m)`. -/
theorem hasSum_eta_nat (m : ℕ) (hm : m ≠ 0) :
    HasSum (etaSummand m)
      ((1 - 2 * (1 / 2 : ℝ) ^ (2 * m)) * ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * m)) :=
  hasSum_eta_of_zeta m _ (hasSum_zeta_nat hm).summable.hasSum

/-- **η(2) = π²/12**, the alternating sum of inverse squares, re-derived uniformly
    from the master lemma (cf. `basel-problem-oq-11`). -/
theorem hasSum_eta_two : HasSum (etaSummand 1) (π ^ 2 / 12) := by
  have h := hasSum_eta_of_zeta 1 _ hasSum_zeta_two
  have hc : (1 - 2 * (1 / 2 : ℝ) ^ (2 * 1)) * (π ^ 2 / 6) = π ^ 2 / 12 := by norm_num; ring
  rwa [hc] at h

/-- **η(4) = 7π⁴/720** — recovers the parent entry `basel-problem-oq-14`. -/
theorem hasSum_eta_four : HasSum (etaSummand 2) (7 * π ^ 4 / 720) := by
  have h := hasSum_eta_of_zeta 2 _ hasSum_zeta_four
  have hc : (1 - 2 * (1 / 2 : ℝ) ^ (2 * 2)) * (π ^ 4 / 90) = 7 * π ^ 4 / 720 := by norm_num; ring
  rwa [hc] at h

/-- η(2) in `tsum` form: `∑' n, (-1)^(n+1)/n² = π²/12`. -/
theorem tsum_eta_two : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 = π ^ 2 / 12 :=
  hasSum_eta_two.tsum_eq

/-- η(4) in `tsum` form: `∑' n, (-1)^(n+1)/n⁴ = 7π⁴/720`. -/
theorem tsum_eta_four : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 = 7 * π ^ 4 / 720 :=
  hasSum_eta_four.tsum_eq

end BaselEtaZeta

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_even_zeta`   | ∑_k 1/(2k)^(2m) = (1/2)^(2m) · ζ(2m) |
  | `hasSum_eta_of_zeta` | master: η(2m) = (1 − 2·(1/2)^(2m)) · Z for any zeta witness Z |
  | `eta_coeff_eq`       | 1 − 2·(1/2)^(2m) = 1 − 2^{1−2m} |
  | `hasSum_eta_nat`     | uniform: η(2m) = (1 − 2^{1−2m}) ζ(2m) via `hasSum_zeta_nat` |
  | `hasSum_eta_two`     | η(2) = π²/12 (uniform re-derivation; cf. oq-11) |
  | `hasSum_eta_four`    | η(4) = 7π⁴/720 (recovers parent oq-14) |
  | `tsum_eta_two/four`  | tsum forms |

  Built entirely from Mathlib's `hasSum_zeta_nat` family and the even/odd series
  split `HasSum.even_add_odd`. The parity split is captured once, abstractly, in
  `hasSum_eta_of_zeta`; everything else is specialisation.

  **Sorries**: 0
  **Axioms**: 0
-/
