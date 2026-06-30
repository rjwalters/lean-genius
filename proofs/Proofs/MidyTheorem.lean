/-
# Midy's Theorem: Complementary Halves of Repeating Decimals

Let `p` be a prime other than the base divisors (e.g. `p ≠ 2, 5` in base 10) and
suppose the repeating block of `1/p` in base `b` has *even* period length `2k`.
Midy's theorem states: if the `2k`-digit repeating block is split into two halves
of `k` digits each, the two halves sum to `bᵏ - 1` (a string of `k` nines in
base 10).

The repeating block (repetend) of `1/p` of period `d` is the integer
`N = (b^d - 1) / p`. With `d = 2k` even we prove the two halves
`N / bᵏ` (high digits) and `N % bᵏ` (low digits) satisfy

    N / bᵏ + N % bᵏ = bᵏ - 1.

## Structure

1. `midy_kernel` — the pure arithmetic heart: for `N = (bᵏ-1)·m` with `1 ≤ m ≤ bᵏ`,
   the two base-`bᵏ` halves of `N` sum to `bᵏ - 1`. (no number theory)
2. `pow_half_orderOf_eq_neg_one` — in a field, an element of order `2k` satisfies
   `xᵏ = -1`. (the "even period" hypothesis made algebraic)
3. `period_even_dvd` — even period `2k` of `b` mod `p` gives `p ∣ bᵏ + 1`.
4. `midy_theorem` — combines the kernel with the divisibility `p ∣ bᵏ + 1`
   (equivalently, even period) to conclude the halves sum to `bᵏ - 1`.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace MidyTheorem

open Nat

/-!
## 1. Arithmetic kernel
-/

/-- The arithmetic core of Midy's theorem. If `N = (bᵏ - 1)·m` with `1 ≤ m ≤ bᵏ`,
then splitting `N` into its high and low base-`bᵏ` halves gives two numbers that
sum to `bᵏ - 1`. Concretely the quotient is `m - 1` and the remainder is `bᵏ - m`. -/
theorem midy_kernel (b k m : ℕ) (hb : 2 ≤ b) (hm1 : 1 ≤ m) (hm2 : m ≤ b ^ k) :
    (b ^ k - 1) * m / b ^ k + (b ^ k - 1) * m % b ^ k = b ^ k - 1 := by
  have hbk : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
  -- Decompose N = (bᵏ - m) + (m - 1)·bᵏ  (a remainder plus a multiple of bᵏ).
  have hkey : (b ^ k - 1) * m = (b ^ k - m) + (m - 1) * b ^ k := by
    zify [hbk, hm1, hm2]
    ring
  have hr : (b ^ k - 1) * m % b ^ k = b ^ k - m := by
    rw [hkey, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hq : (b ^ k - 1) * m / b ^ k = m - 1 := by
    rw [hkey, Nat.add_mul_div_right _ _ (show 0 < b ^ k by omega),
      Nat.div_eq_of_lt (show b ^ k - m < b ^ k by omega), Nat.zero_add]
  rw [hq, hr]
  omega

/-!
## 2. Algebraic content: order `2k` forces `xᵏ = -1`
-/

/-- In a field, an element of multiplicative order `2k` (with `k ≥ 1`) satisfies
`xᵏ = -1`: indeed `(xᵏ)² = 1` so `xᵏ = ±1`, and `xᵏ = 1` is impossible since the
order `2k` does not divide `k`. -/
theorem pow_half_orderOf_eq_neg_one {F : Type*} [Field F] {x : F} {k : ℕ}
    (hk : 1 ≤ k) (hord : orderOf x = 2 * k) : x ^ k = -1 := by
  have hone : x ^ k * x ^ k = 1 := by
    rw [← pow_add]
    have hkk : k + k = 2 * k := by ring
    rw [hkk, ← hord, pow_orderOf_eq_one]
  have h0 : (x ^ k - 1) * (x ^ k + 1) = 0 := by linear_combination hone
  rcases mul_eq_zero.mp h0 with h | h
  · exfalso
    have hx1 : x ^ k = 1 := by linear_combination h
    have hdvd : orderOf x ∣ k := orderOf_dvd_of_pow_eq_one hx1
    rw [hord] at hdvd
    have : 2 * k ≤ k := Nat.le_of_dvd (by omega) hdvd
    omega
  · linear_combination h

/-!
## 3. Number-theoretic bridge: even period gives `p ∣ bᵏ + 1`
-/

/-- If the multiplicative order of `b` modulo the prime `p` is `2k` (i.e. the
period of `1/p` in base `b` is `2k`), then `p ∣ bᵏ + 1`. This is the hypothesis
needed by `midy_theorem`, derived from the "even period" condition. -/
theorem period_even_dvd (p b k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (hperiod : orderOf (b : ZMod p) = 2 * k) : p ∣ b ^ k + 1 := by
  have hx : (b : ZMod p) ^ k = -1 := pow_half_orderOf_eq_neg_one hk hperiod
  have hzero : ((b ^ k + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [hx]; ring
  exact (ZMod.natCast_eq_zero_iff _ p).mp hzero

/-!
## 4. Midy's theorem
-/

/-- **Midy's theorem.** Let `p ≥ 2`, `b ≥ 2`, `k ≥ 1`, and suppose `p ∣ bᵏ + 1`
(this holds exactly when the period of `1/p` in base `b` is the even number `2k`;
see `period_even_dvd`). Then the repetend `N = (b^(2k) - 1)/p` of `1/p`, split into
its high and low base-`bᵏ` halves, has halves summing to `bᵏ - 1` — a block of
`k` nines in base 10. -/
theorem midy_theorem (p b k : ℕ) (hp : 2 ≤ p) (_hk : 1 ≤ k) (hb : 2 ≤ b)
    (hdvd : p ∣ b ^ k + 1) :
    (b ^ (2 * k) - 1) / p / b ^ k + (b ^ (2 * k) - 1) / p % b ^ k = b ^ k - 1 := by
  obtain ⟨m, hm⟩ := hdvd
  have hbk : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
  -- m ≥ 1, else p·m = 0 ≠ bᵏ + 1.
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · subst h0; simp only [mul_zero] at hm; omega
    · exact h
  -- m ≤ bᵏ, since 2m ≤ p·m = bᵏ + 1 ≤ 2·bᵏ.
  have hm2 : m ≤ b ^ k := by
    have h2m : 2 * m ≤ p * m := Nat.mul_le_mul hp (le_refl m)
    rw [← hm] at h2m
    omega
  -- The repetend factors exactly: b^(2k) - 1 = p · ((bᵏ - 1)·m).
  have hpow : b ^ (2 * k) = (b ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]
  have ht : (b ^ k) ^ 2 - 1 = (b ^ k - 1) * (b ^ k + 1) := by
    have h1 : 1 ≤ (b ^ k) ^ 2 := Nat.one_le_pow 2 (b ^ k) (by omega)
    zify [hbk, h1]
    ring
  have hfact : b ^ (2 * k) - 1 = p * ((b ^ k - 1) * m) := by
    rw [hpow, ht, hm]; ring
  have hNval : (b ^ (2 * k) - 1) / p = (b ^ k - 1) * m := by
    rw [hfact, Nat.mul_div_cancel_left _ (show 0 < p by omega)]
  rw [hNval]
  exact midy_kernel b k m hb hm1 hm2

/-!
## Worked example: `1/7 = 0.\overline{142857}`, period `6 = 2·3`

The repetend is `142857`; halves `142 + 857 = 999 = 10³ - 1`.
Here `p = 7`, `b = 10`, `k = 3`, and `7 ∣ 10³ + 1 = 1001 = 7·11·13`.
-/

example : (10 ^ (2 * 3) - 1) / 7 / 10 ^ 3 + (10 ^ (2 * 3) - 1) / 7 % 10 ^ 3 = 10 ^ 3 - 1 := by
  decide

example : (7 : ℕ) ∣ 10 ^ 3 + 1 := by decide

end MidyTheorem
