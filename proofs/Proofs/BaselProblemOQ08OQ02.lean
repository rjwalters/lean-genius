/-
# Basel Problem OQ-08-OQ-02: the value ζ(6) = π⁶/945 and the ζ(2k)/π^{2k} ratio chain

## Open Question
Formalize `∑' n, 1 / n⁶ = π⁶ / 945`, the next even-argument value after the Basel
problem `ζ(2) = π²/6` and its parent `ζ(4) = π⁴/90`, by instantiating Mathlib's
even-zeta formula `hasSum_zeta_nat` / `riemannZeta_two_mul_nat` at `k = 3`, plus the
dimensionless (π-free) Euler ratio `ζ(6) / ζ(2)³ = 8/35`.

## Approach
Mathlib proves the general even-zeta formula
`hasSum_zeta_nat : HasSum (fun n => 1/n^(2k)) ((-1)^(k+1)·2^(2k-1)·π^(2k)·B_{2k}/(2k)!)`.
Unlike `k = 1, 2` (which have packaged `bernoulli'_two`, `bernoulli'_four`), Mathlib
provides no `bernoulli'_six`, so we first compute `bernoulli 6 = 1/42` from the defining
recurrence (`bernoulli'_def`, using that `bernoulli' 5 = 0` as an odd index `> 1`).
Substituting `k = 3` then gives `2⁵·π⁶·(1/42)/720 = π⁶/945`.

The companion `riemannZeta_two_mul_nat` gives the value of the analytically-continued
`riemannZeta 6`. Finally, dividing `ζ(6) = π⁶/945` by `ζ(2)³ = π⁶/216` cancels π,
leaving the rational `216/945 = 8/35`, the degree-6 analogue of the parent's `ζ(4)/ζ(2)² = 2/5`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace BaselProblemOQ08OQ02

open Real BigOperators

/-- **The sixth Bernoulli number `B₆ = 1/42`.** Mathlib packages `bernoulli'_two` and
`bernoulli'_four` but not `bernoulli'_six`; we compute it from the defining recurrence
`bernoulli'_def`, using that the odd-index `bernoulli' 5` vanishes. -/
theorem bernoulli_six : (bernoulli 6 : ℚ) = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (6 : ℕ) ≠ 1), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h5,
    show Nat.choose 6 1 = 6 from rfl, show Nat.choose 6 2 = 15 from rfl,
    show Nat.choose 6 3 = 20 from rfl, show Nat.choose 6 4 = 15 from rfl,
    show Nat.choose 6 5 = 6 from rfl]

/-- The summable family `n ↦ 1/n⁶` has sum `π⁶/945`, the `k = 3` instance of Mathlib's
even-zeta formula `hasSum_zeta_nat`. -/
theorem hasSum_one_div_nat_pow_six :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 6) (π ^ 6 / 945) := by
  convert hasSum_zeta_nat (by norm_num : (3 : ℕ) ≠ 0) using 1
  rw [show (2 * 3 : ℕ) = 6 from rfl, bernoulli_six]
  norm_num [Nat.factorial]
  ring

/-- **ζ(6) = π⁶/945.** The infinite sum `∑' n, 1/n⁶` over the naturals equals `π⁶/945`. -/
theorem tsum_one_div_nat_pow_six :
    ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6 = π ^ 6 / 945 :=
  hasSum_one_div_nat_pow_six.tsum_eq

/-- The Riemann zeta function at `6` equals `π⁶/945`, via Mathlib's
`riemannZeta_two_mul_nat` at `k = 3`. -/
theorem riemannZeta_six_eq : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (by norm_num : (3 : ℕ) ≠ 0)
  rw [show (2 * 3 : ℕ) = 6 from rfl, bernoulli_six,
    show (2 : ℂ) * ((3 : ℕ) : ℂ) = 6 by norm_num] at h
  rw [h]
  push_cast [Nat.factorial]
  ring

/-- **Euler's ratio `ζ(6) / ζ(2)³ = 8/35`.** Dividing the even-zeta values
`ζ(6) = π⁶/945` and `ζ(2) = π²/6` makes π cancel (`ζ(2)³ = π⁶/216`), leaving the
rational `216/945 = 8/35`. This is the degree-6 analogue of `ζ(4)/ζ(2)² = 2/5`. -/
theorem tsum_six_div_tsum_two_cube :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 6) / (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 3 = 8 / 35 := by
  rw [tsum_one_div_nat_pow_six, hasSum_zeta_two.tsum_eq]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h6 : (π : ℝ) ^ 6 ≠ 0 := pow_ne_zero _ hπ
  field_simp
  ring

end BaselProblemOQ08OQ02
