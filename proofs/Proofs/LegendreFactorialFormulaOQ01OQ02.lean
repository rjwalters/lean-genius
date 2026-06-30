/-
# Trailing Zeros of `n!` in Base Ten

The number of zeros that `n!` ends with in base `10` is the largest `k` with
`10ᵏ ∣ n!`.  Since `10 = 2 · 5` and `2`, `5` are distinct primes, this count is

  `min (v₂(n!)) (v₅(n!))`,

where `vₚ` is the `p`-adic valuation.  The two-adic valuation of a factorial
always dominates the five-adic one (there are at least as many factors of `2` as
of `5`), so the minimum is realised by the five-adic side:

  `#trailing zeros of n! = v₅(n!) = (n − S₅(n)) / 4`,

with `S₅(n)` the base-`5` digit sum (Legendre's digit-sum form, specialised to
`p = 5`).  This is the open question `oq-02` of the Legendre's-formula entry.

We give the faithful order-theoretic statement: `v₅(n!)` is the **greatest** `k`
with `10ᵏ ∣ n!` (`trailingZeros_isGreatest`), then read off the two defining
properties (`10^{v₅} ∣ n!` and `¬ 10^{v₅+1} ∣ n!`), the `min` identity, and the
closed digit-sum form.  Everything is fully verified with no `sorry` and no extra
axioms.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Nat Finset

namespace LegendreFactorialFormulaOQ01OQ02

/-- Dividing by a larger denominator gives a smaller quotient:
`a ≤ b` and `0 < a` imply `n / b ≤ n / a`. -/
private theorem div_le_div_of_denom_le {n a b : ℕ} (hab : a ≤ b) (ha : 0 < a) :
    n / b ≤ n / a := by
  rw [Nat.le_div_iff_mul_le ha]
  exact le_trans (Nat.mul_le_mul (Nat.le_refl _) hab) (Nat.div_mul_le_self n b)

/-- **The two-adic valuation of `n!` dominates the five-adic one.**
Termwise, Legendre's floor sums satisfy `⌊n / 5ⁱ⌋ ≤ ⌊n / 2ⁱ⌋`, because `2ⁱ ≤ 5ⁱ`. -/
theorem padicValNat_five_le_two (n : ℕ) :
    padicValNat 5 (n !) ≤ padicValNat 2 (n !) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [padicValNat_factorial (p := 5) (n := n) (b := n + 1)
        (Nat.lt_succ_of_le (Nat.log_le_self 5 n)),
      padicValNat_factorial (p := 2) (n := n) (b := n + 1)
        (Nat.lt_succ_of_le (Nat.log_le_self 2 n))]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_denom_le (Nat.pow_le_pow_left (by norm_num) i) (pow_pos (by norm_num) i)

/-- **Main theorem.**  The five-adic valuation of `n!` is the greatest `k` for
which `10ᵏ` divides `n!`; equivalently, it is the number of trailing zeros of
`n!` in base ten.

Membership uses `10^{v₅} = 2^{v₅} · 5^{v₅}` with both prime powers dividing `n!`
(the `2`-power because `v₅ ≤ v₂`) and `2^{v₅}`, `5^{v₅}` coprime.  The upper
bound is `5ᵏ ∣ 10ᵏ ∣ n! ⟹ k ≤ v₅`. -/
theorem trailingZeros_isGreatest (n : ℕ) :
    IsGreatest {k | 10 ^ k ∣ (n !)} (padicValNat 5 (n !)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  set Z := padicValNat 5 (n !) with hZ
  constructor
  · -- `10^Z ∣ n!`
    show 10 ^ Z ∣ (n !)
    have hv5 : (5 : ℕ) ^ Z ∣ (n !) := pow_padicValNat_dvd
    have hv2 : (2 : ℕ) ^ Z ∣ (n !) :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mpr (padicValNat_five_le_two n)
    have hcop : Nat.Coprime (2 ^ Z) (5 ^ Z) := Nat.Coprime.pow _ _ (by decide)
    have h10 : (10 : ℕ) = 2 * 5 := by norm_num
    rw [h10, mul_pow]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hv2 hv5
  · -- any `k` with `10^k ∣ n!` satisfies `k ≤ Z`
    intro k hk
    have h5 : (5 : ℕ) ^ k ∣ (n !) :=
      dvd_trans (pow_dvd_pow_of_dvd (by norm_num) k) hk
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp h5

/-- `10^{v₅(n!)}` divides `n!`: there are at least `v₅(n!)` trailing zeros. -/
theorem ten_pow_v5_dvd_factorial (n : ℕ) :
    10 ^ (padicValNat 5 (n !)) ∣ (n !) :=
  (trailingZeros_isGreatest n).1

/-- `10^{v₅(n!)+1}` does not divide `n!`: there are no more than `v₅(n!)` trailing
zeros. -/
theorem not_ten_pow_succ_dvd_factorial (n : ℕ) :
    ¬ (10 ^ (padicValNat 5 (n !) + 1) ∣ (n !)) := by
  intro h
  have := (trailingZeros_isGreatest n).2 h
  omega

/-- **The trailing-zero count as a minimum of valuations.**
`min (v₂(n!)) (v₅(n!)) = v₅(n!)`, since the five-adic valuation is the smaller. -/
theorem trailingZeros_eq_min (n : ℕ) :
    min (padicValNat 2 (n !)) (padicValNat 5 (n !)) = padicValNat 5 (n !) :=
  min_eq_right (padicValNat_five_le_two n)

/-- **Closed digit-sum form.**  The number of trailing zeros of `n!` equals
`(n − S₅(n)) / 4`, where `S₅(n)` is the sum of the base-`5` digits of `n`. -/
theorem trailingZeros_eq_digit_form (n : ℕ) :
    min (padicValNat 2 (n !)) (padicValNat 5 (n !))
      = (n - (Nat.digits 5 n).sum) / 4 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [trailingZeros_eq_min]
  have h := sub_one_mul_padicValNat_factorial (p := 5) n
  rw [show (5 : ℕ) - 1 = 4 from rfl] at h
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]

/-- Worked instance: `10!` ends in exactly two zeros.
`v₅(10!) = ⌊10/5⌋ = 2`, and indeed `10! = 3628800`. -/
example : padicValNat 5 (10 !) = 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [padicValNat_factorial (p := 5) (n := 10) (b := 2)
    (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

/-- The greatest power of `10` dividing `10!` is `10² = 100`. -/
example : IsGreatest {k | 10 ^ k ∣ (10 !)} 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hv5 : padicValNat 5 (10 !) = 2 := by
    rw [padicValNat_factorial (p := 5) (n := 10) (b := 2)
      (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
    decide
  have := trailingZeros_isGreatest 10
  rwa [hv5] at this

end LegendreFactorialFormulaOQ01OQ02
