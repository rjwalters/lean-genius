/-
# Basel Problem OQ-15: the value ζ(8) = π⁸/9450 and the ζ(8)/ζ(2)⁴ ratio

## Open Question
Formalize `∑' n, 1 / n⁸ = π⁸ / 9450`, the next even-argument value after
`ζ(2) = π²/6`, `ζ(4) = π⁴/90`, and `ζ(6) = π⁶/945`, by instantiating Mathlib's
even-zeta formula `hasSum_zeta_nat` / `riemannZeta_two_mul_nat` at `k = 4`, plus the
dimensionless (π-free) Euler ratio `ζ(8) / ζ(2)⁴ = 24/175`.

## Approach
Mathlib proves the general even-zeta formula
`hasSum_zeta_nat : HasSum (fun n => 1/n^(2k)) ((-1)^(k+1)·2^(2k-1)·π^(2k)·B_{2k}/(2k)!)`.
Mathlib packages `bernoulli'_two`, `bernoulli'_four`, `bernoulli'_six` but not
`bernoulli'_eight`, so we first compute `bernoulli 8 = -1/30` from the defining
recurrence (`bernoulli'_def`), using that the odd-index `bernoulli' 3, 5, 7` vanish.
Substituting `k = 4` then gives `2⁷·π⁸·(-1/30)/8! = π⁸/9450` (since `128/(30·40320) = 1/9450`).

The companion `riemannZeta_two_mul_nat` gives the value of the analytically-continued
`riemannZeta 8`. Finally, dividing `ζ(8) = π⁸/9450` by `ζ(2)⁴ = π⁸/1296` cancels π,
leaving the rational `1296/9450 = 24/175`, the degree-8 analogue of the parent chain's
`ζ(4)/ζ(2)² = 2/5` and `ζ(6)/ζ(2)³ = 8/35`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace BaselProblemOQ15

open Real BigOperators

/-- **The eighth Bernoulli number `B₈ = -1/30`.** Mathlib packages `bernoulli'_two`,
`bernoulli'_four`, and `bernoulli'_six` but not `bernoulli'_eight`; we compute it from
the defining recurrence `bernoulli'_def`, using that the odd-index `bernoulli' 3, 5, 7`
vanish. -/
theorem bernoulli_eight : (bernoulli 8 : ℚ) = -1 / 30 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  -- Mathlib packages `bernoulli'_two` and `bernoulli'_four` but not `bernoulli'_six`;
  -- compute `B'₆ = 1/42` from the recurrence (this is the only Bernoulli value missing).
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h5,
      show Nat.choose 6 1 = 6 from rfl, show Nat.choose 6 2 = 15 from rfl,
      show Nat.choose 6 3 = 20 from rfl, show Nat.choose 6 4 = 15 from rfl,
      show Nat.choose 6 5 = 6 from rfl]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (8 : ℕ) ≠ 1), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h3, h5, h6, h7,
    show Nat.choose 8 1 = 8 from rfl, show Nat.choose 8 2 = 28 from rfl,
    show Nat.choose 8 3 = 56 from rfl, show Nat.choose 8 4 = 70 from rfl,
    show Nat.choose 8 5 = 56 from rfl, show Nat.choose 8 6 = 28 from rfl,
    show Nat.choose 8 7 = 8 from rfl]

/-- The summable family `n ↦ 1/n⁸` has sum `π⁸/9450`, the `k = 4` instance of Mathlib's
even-zeta formula `hasSum_zeta_nat`. -/
theorem hasSum_one_div_nat_pow_eight :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 8) (π ^ 8 / 9450) := by
  convert hasSum_zeta_nat (by norm_num : (4 : ℕ) ≠ 0) using 1
  rw [show (2 * 4 : ℕ) = 8 from rfl, bernoulli_eight]
  norm_num [Nat.factorial]
  ring

/-- **ζ(8) = π⁸/9450.** The infinite sum `∑' n, 1/n⁸` over the naturals equals `π⁸/9450`. -/
theorem tsum_one_div_nat_pow_eight :
    ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8 = π ^ 8 / 9450 :=
  hasSum_one_div_nat_pow_eight.tsum_eq

/-- The Riemann zeta function at `8` equals `π⁸/9450`, via Mathlib's
`riemannZeta_two_mul_nat` at `k = 4`. -/
theorem riemannZeta_eight_eq : riemannZeta 8 = (π : ℂ) ^ 8 / 9450 := by
  have h := riemannZeta_two_mul_nat (by norm_num : (4 : ℕ) ≠ 0)
  rw [show (2 * 4 : ℕ) = 8 from rfl, bernoulli_eight,
    show (2 : ℂ) * ((4 : ℕ) : ℂ) = 8 by norm_num] at h
  rw [h]
  push_cast [Nat.factorial]
  ring

/-- **Euler's ratio `ζ(8) / ζ(2)⁴ = 24/175`.** Dividing the even-zeta values
`ζ(8) = π⁸/9450` and `ζ(2) = π²/6` makes π cancel (`ζ(2)⁴ = π⁸/1296`), leaving the
rational `1296/9450 = 24/175`. This continues the chain `ζ(4)/ζ(2)² = 2/5`,
`ζ(6)/ζ(2)³ = 8/35`. -/
theorem tsum_eight_div_tsum_two_fourth :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8) / (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 4 = 24 / 175 := by
  rw [tsum_one_div_nat_pow_eight, hasSum_zeta_two.tsum_eq]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h8 : (π : ℝ) ^ 8 ≠ 0 := pow_ne_zero _ hπ
  field_simp
  ring

end BaselProblemOQ15
