/-
# Basel Problem OQ-08-OQ-02-OQ-01: the value ζ(8) = π⁸/9450 and the π-free ratio ζ(8)/ζ(2)⁴

## Open Question
Formalize `∑' n, 1 / n⁸ = π⁸ / 9450`, the next even-argument value after the parent
`ζ(6) = π⁶/945` (itself following `ζ(2) = π²/6` and `ζ(4) = π⁴/90`), by instantiating
Mathlib's even-zeta formula `hasSum_zeta_nat` / `riemannZeta_two_mul_nat` at `k = 4`,
plus the dimensionless (π-free) Euler ratio `ζ(8) / ζ(2)⁴ = 24/175`.

## Approach
Mathlib proves the general even-zeta formula
`hasSum_zeta_nat : HasSum (fun n => 1/n^(2k)) ((-1)^(k+1)·2^(2k-1)·π^(2k)·B_{2k}/(2k)!)`.
As with `ζ(6)`, Mathlib packages `bernoulli'_two`, `bernoulli'_four` (both `@[simp]`)
but provides no `bernoulli'_six` or `bernoulli'_eight`. We first compute
`bernoulli 6 = 1/42` and then `bernoulli 8 = -1/30` from the defining recurrence
`bernoulli'_def`, supplying the non-`simp` summands `bernoulli' 5 = bernoulli' 7 = 0`
(odd indices `> 1`) and the freshly-computed `bernoulli' 6 = 1/42`.
Substituting `k = 4` then gives `2⁷·π⁸·(−1/30)/40320 = π⁸/9450`.

The companion `riemannZeta_two_mul_nat` gives the value of the analytically-continued
`riemannZeta 8`. Finally, dividing `ζ(8) = π⁸/9450` by `ζ(2)⁴ = π⁸/1296` cancels π,
leaving the rational `1296/9450 = 24/175`, the degree-8 analogue of the parent's
`ζ(6)/ζ(2)³ = 8/35` and `ζ(4)/ζ(2)² = 2/5`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace BaselProblemOQ08OQ02OQ01

open Real BigOperators

/-- **The sixth Bernoulli number `B₆ = 1/42`.** Mathlib packages `bernoulli'_two` and
`bernoulli'_four` but not `bernoulli'_six`; we compute it from the defining recurrence
`bernoulli'_def`, using that the odd-index `bernoulli' 5` vanishes. (Identical to the
parent ζ(6) entry's lemma; reproduced here because `B₆` is a summand of the `B₈`
recurrence.) -/
theorem bernoulli_six : (bernoulli 6 : ℚ) = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (6 : ℕ) ≠ 1), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h5,
    show Nat.choose 6 1 = 6 from rfl, show Nat.choose 6 2 = 15 from rfl,
    show Nat.choose 6 3 = 20 from rfl, show Nat.choose 6 4 = 15 from rfl,
    show Nat.choose 6 5 = 6 from rfl]

/-- **The eighth Bernoulli number `B₈ = −1/30`.** Computed from `bernoulli'_def`, using
that the odd-index `bernoulli' 5` and `bernoulli' 7` vanish and that `bernoulli' 6 = 1/42`
(from `bernoulli_six`); the lower summands `bernoulli' 0..4` are resolved by their
`@[simp]` lemmas. Remarkably `B₈ = B₄ = −1/30`. -/
theorem bernoulli_eight : (bernoulli 8 : ℚ) = -1 / 30 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide : (6 : ℕ) ≠ 1)]; exact bernoulli_six
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (8 : ℕ) ≠ 1), bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h5, h6, h7,
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
rational `1296/9450 = 24/175`. This is the degree-8 analogue of `ζ(6)/ζ(2)³ = 8/35`
and `ζ(4)/ζ(2)² = 2/5`. -/
theorem tsum_eight_div_tsum_two_pow_four :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 8) / (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) ^ 4 = 24 / 175 := by
  rw [tsum_one_div_nat_pow_eight, hasSum_zeta_two.tsum_eq]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h8 : (π : ℝ) ^ 8 ≠ 0 := pow_ne_zero _ hπ
  field_simp
  ring

end BaselProblemOQ08OQ02OQ01
