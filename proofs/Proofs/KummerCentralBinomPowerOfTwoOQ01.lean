import Mathlib

/-
# Exactly one factor of two in the central binomial coefficient

## The open question

The parent entry (`kummer-theorem-oq-04`) establishes the closed form for the
`2`-adic valuation of the central binomial coefficient,
`v₂(C(2n, n)) = s₂(n)`, where `s₂(n)` is the binary digit sum of `n`, and records
the *forward* fact that for a power of two `n = 2^k` the valuation drops to `1`.
It leaves open the **converse**: are powers of two the *only* `n` for which
`C(2n, n)` is divisible by `2` exactly once?

## Answer: yes — a sharp biconditional

$$\nu_2\binom{2n}{n} = 1 \iff n = 2^k \text{ for some } k.$$

Equivalently: `C(2n, n)` is divisible by `2` but **not** by `4` precisely when `n`
is a power of two.

### Why this is true

By the parent's closed form `v₂(C(2n, n)) = s₂(n)`, the statement
`v₂(C(2n, n)) = 1` is equivalent to `s₂(n) = 1`, i.e. the binary expansion of `n`
has a single `1`-bit.  The genuinely new content is the elementary characterisation

  `s₂(n) = 1  ↔  n = 2^k for some k`,

which is **not** in Mathlib (Mathlib knows `bitIndices (2^k) = [k]`, but not the
digit-sum characterisation).  The forward direction is proved by strong induction
peeling the last binary digit `n % 2`:

* if `n` is odd, the remaining digits must sum to `0`, forcing `n / 2 = 0`, so
  `n = 1 = 2^0`;
* if `n` is even, the digits of `n / 2` still sum to `1`, so by induction
  `n / 2 = 2^j` and hence `n = 2^{j+1}`.

The reverse direction multiplies out `digits 2 (2^k)` via `digits_base_pow_mul`.

## What Mathlib already has

`Nat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits` (Kummer / Legendre in
digit-sum form), `Nat.centralBinom`, and `digits_base_pow_mul`.  It does **not**
package `s₂(n) = 1 ↔ n = 2^k` nor the central-binomial biconditional below.

## Results in this file (original content, 0 axioms / 0 sorries)

* `sum_digits_two_eq_one_iff`               : **the new lemma** `s₂(n) = 1 ↔ ∃ k, n = 2^k`
* `padicValNat_two_centralBinom`            : the parent closed form, re-derived here
                                              so the file is self-contained
* `padicValNat_two_centralBinom_eq_one_iff` : **the headline** `v₂(C(2n,n)) = 1 ↔ ∃ k, n = 2^k`
* `two_dvd_centralBinom_not_four_dvd_iff`   : `2 ∣ C(2n,n) ∧ ¬ 4 ∣ C(2n,n) ↔ ∃ k, n = 2^k`
                                              (the "exactly one factor of two" phrasing)
-/

namespace KummerCentralBinomPowTwo

open Nat

/-- **Doubling-invariance of the binary digit sum.** Multiplying by the base `2`
prepends a trailing `0` digit, leaving the digit sum unchanged: `s₂(2n) = s₂(n)`. -/
theorem sum_digits_two_mul (n : ℕ) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [Nat.digits_base_mul one_lt_two hn]; simp

/-- For `n > 0` the binary digit sum is positive (the leading digit is nonzero). -/
theorem sum_digits_two_pos {n : ℕ} (hn : 0 < n) : 0 < (Nat.digits 2 n).sum := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  exact Nat.sum_pos_iff_exists_pos.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hn.ne')⟩

/-- The binary digit sum vanishes only for `0`. -/
theorem sum_digits_two_eq_zero_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 0 ↔ n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp only [hn.ne', iff_false]
    exact (sum_digits_two_pos hn).ne'

/-- **The new lemma.** A natural number has binary digit sum `1` exactly when it is
a power of two.  Equivalently, `n` has a single `1`-bit iff `n = 2^k`. -/
theorem sum_digits_two_eq_one_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · -- forward: strong induction peeling the last binary digit
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at h
      · rw [Nat.digits_def' one_lt_two hn, List.sum_cons] at h
        -- h : n % 2 + (digits 2 (n / 2)).sum = 1
        have hlt : n / 2 < n := Nat.div_lt_self hn one_lt_two
        rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
        · -- n even: the digits of n / 2 still sum to 1
          rw [h0, Nat.zero_add] at h
          obtain ⟨j, hj⟩ := ih (n / 2) hlt h
          refine ⟨j + 1, ?_⟩
          have hn2 : n = 2 * (n / 2) := by omega
          rw [hn2, hj]; ring
        · -- n odd: the remaining digits must vanish, forcing n / 2 = 0
          rw [h1] at h
          have hz : (Nat.digits 2 (n / 2)).sum = 0 := by omega
          have hd0 : n / 2 = 0 := (sum_digits_two_eq_zero_iff _).mp hz
          refine ⟨0, ?_⟩
          have : n = 1 := by omega
          rw [this]; norm_num
  · -- reverse: digits 2 (2^k) = 0…0 ++ [1]
    rintro ⟨k, rfl⟩
    rw [show (2 : ℕ) ^ k = 2 ^ k * 1 by ring, Nat.digits_base_pow_mul one_lt_two one_pos]
    simp

/-- **The 2-adic valuation of the central binomial coefficient is the binary digit
sum** (the parent closed form, re-derived here to keep this file self-contained).
`v₂(C(2n, n)) = s₂(n)`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : n ≤ 2 * n := by omega
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n) h
  have e1 : (2 : ℕ) * n - n = n := by omega
  rw [e1, sum_digits_two_mul] at key
  rw [Nat.centralBinom_eq_two_mul_choose]
  omega

/-- **The headline biconditional.** The central binomial coefficient `C(2n, n)` is
divisible by `2` exactly once iff `n` is a power of two:
`v₂(C(2n, n)) = 1 ↔ ∃ k, n = 2^k`.  This closes the converse left open by the
parent entry. -/
theorem padicValNat_two_centralBinom_eq_one_iff (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = 1 ↔ ∃ k, n = 2 ^ k := by
  rw [padicValNat_two_centralBinom]
  exact sum_digits_two_eq_one_iff n

/-- **The "exactly one factor of two" phrasing.** `C(2n, n)` is divisible by `2`
but not by `4` precisely when `n` is a power of two. -/
theorem two_dvd_centralBinom_not_four_dvd_iff (n : ℕ) :
    (2 ∣ Nat.centralBinom n ∧ ¬ (4 ∣ Nat.centralBinom n)) ↔ ∃ k, n = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : Nat.centralBinom n ≠ 0 := Nat.centralBinom_ne_zero n
  have d2 : 2 ∣ Nat.centralBinom n ↔ 1 ≤ padicValNat 2 (Nat.centralBinom n) := by
    conv_lhs => rw [← pow_one (2 : ℕ)]
    exact padicValNat_dvd_iff_le hne
  have d4 : 4 ∣ Nat.centralBinom n ↔ 2 ≤ padicValNat 2 (Nat.centralBinom n) := by
    conv_lhs => rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact padicValNat_dvd_iff_le hne
  rw [d2, d4, ← padicValNat_two_centralBinom_eq_one_iff n]
  omega

/-! ### Worked numeric witnesses (0-axiom, kernel `decide`)

`n = 4 = 2²` is a power of two, so `C(8, 4) = 70 = 2 · 35` has `v₂ = 1`
(`s₂(4) = 1`).  `n = 3` is not, so `C(6, 3) = 20 = 2² · 5` has `v₂ = 2`
(`s₂(3) = 2`). -/

example : Nat.centralBinom 4 = 70 := by decide
example : Nat.centralBinom 3 = 20 := by decide

-- `n = 4 = 2²` is a power of two, so `C(8, 4) = 70` is divisible by `2` exactly once.
example : padicValNat 2 (Nat.centralBinom 4) = 1 :=
  (padicValNat_two_centralBinom_eq_one_iff 4).mpr ⟨2, by norm_num⟩

-- `n = 3` is not a power of two, so `C(6, 3) = 20` is divisible by `4`
-- (it carries two factors of `2`).
example : (4 : ℕ) ∣ Nat.centralBinom 3 := by decide

end KummerCentralBinomPowTwo
