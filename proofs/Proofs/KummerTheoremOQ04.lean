import Mathlib

/-
# The 2-adic Valuation of the Central Binomial Coefficient

## The Open Question

Kummer's theorem computes the `p`-adic valuation of a binomial coefficient as the
number of carries when adding in base `p`. A natural and classical specialisation
asks for the *exact* power of `2` dividing the **central binomial coefficient**
`centralBinom n = C(2n, n)`. What is `v₂(C(2n, n))` in closed form?

## Answer: it is the binary digit sum of `n`

$$\nu_2\binom{2n}{n} \;=\; s_2(n)$$

where `s₂(n)` is the sum of the binary digits of `n` (equivalently, the number of
`1`s in the binary expansion of `n`, i.e. its popcount).

### Why this is true

Legendre's formula gives, for a prime `p`,
`(p-1)·v_p(C(n,k)) = s_p(k) + s_p(n-k) - s_p(n)`.  With `p = 2`, `n ↦ 2n`, `k = n`:

  `1 · v₂(C(2n,n)) = s₂(n) + s₂(2n - n) - s₂(2n) = 2·s₂(n) - s₂(2n)`.

Multiplying by `2` shifts every binary digit one place left and inserts a trailing
`0`, so it does not change the digit sum: `s₂(2n) = s₂(n)`.  Hence
`v₂(C(2n,n)) = 2·s₂(n) - s₂(n) = s₂(n)`.

## What Mathlib already has

Mathlib provides Kummer's theorem in digit-sum form
(`Nat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits`) and the central binomial
coefficient `Nat.centralBinom` with `Nat.two_dvd_centralBinom_of_one_le`
(`C(2n,n)` is even for `n ≥ 1`).  It does **not** package the exact valuation
`v₂(C(2n,n)) = s₂(n)`, nor the sharp consequences below.

## Results in this file (original content, all 0 axioms / 0 sorries)

* `sum_digits_two_mul`            : `s₂(2n) = s₂(n)` (digit sum is doubling-invariant)
* `padicValNat_two_centralBinom`  : **the headline** `v₂(C(2n,n)) = s₂(n)`
* `even_centralBinom_iff`         : `C(2n,n)` is even ↔ `0 < n` (sharp: `C(0,0)=1`)
* `two_pow_sum_digits_dvd_centralBinom` /
  `not_two_pow_succ_sum_digits_dvd_centralBinom`
                                  : `2^{s₂(n)}` divides `C(2n,n)` *exactly*
* `padicValNat_two_centralBinom_pow_two` : for `n = 2^k`, `v₂(C(2^{k+1}, 2^k)) = 1`
* `padicValNat_two_centralBinom_pred_pow_two` :
      for `n = 2^k - 1` (all-ones), `v₂(C(2n,n)) = k`
* worked numeric witnesses (`C(6,3)=20=2²·5`, `C(10,5)=252=2²·63`, ...)
-/

namespace KummerCentralBinom

open Nat

/-- **Doubling-invariance of the binary digit sum.** Multiplying by the base `2`
prepends a `0` digit, leaving the digit sum unchanged: `s₂(2n) = s₂(n)`. -/
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

/-- **The 2-adic valuation of the central binomial coefficient is the binary digit
sum.**  `v₂(C(2n, n)) = s₂(n)`.

This is the closed form of Kummer's carry count specialised to `p = 2` and the
diagonal `C(2n, n)`: the number of carries when adding `n + n` in base `2` equals
the number of `1`-bits of `n`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : n ≤ 2 * n := by omega
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n) h
  have e1 : (2 : ℕ) * n - n = n := by omega
  rw [e1, sum_digits_two_mul] at key
  rw [Nat.centralBinom_eq_two_mul_choose]
  -- key : (2 - 1) * v₂(C(2n,n)) = s₂(n) + s₂(n) - s₂(n)
  omega

/-- **Sharp parity of the central binomial coefficient.** `C(2n, n)` is even iff
`n > 0`.  (The only odd value is `C(0,0) = 1`.) Derived directly from the valuation
formula via `s₂(n) > 0 ↔ n > 0`. -/
theorem even_centralBinom_iff (n : ℕ) : Even (Nat.centralBinom n) ↔ 0 < n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [even_iff_two_dvd, ← pow_one (2 : ℕ),
      padicValNat_dvd_iff_le (Nat.centralBinom_ne_zero n), padicValNat_two_centralBinom]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at h
    · exact hn
  · intro hn; exact sum_digits_two_pos hn

/-- **Exact power dividing `C(2n, n)` — divisibility half.** `2^{s₂(n)} ∣ C(2n, n)`. -/
theorem two_pow_sum_digits_dvd_centralBinom (n : ℕ) :
    2 ^ (Nat.digits 2 n).sum ∣ Nat.centralBinom n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← padicValNat_two_centralBinom]
  exact pow_padicValNat_dvd

/-- **Exact power dividing `C(2n, n)` — sharpness half.** No larger power of `2`
divides: `¬ 2^{s₂(n)+1} ∣ C(2n, n)`. -/
theorem not_two_pow_succ_sum_digits_dvd_centralBinom (n : ℕ) :
    ¬ 2 ^ ((Nat.digits 2 n).sum + 1) ∣ Nat.centralBinom n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← padicValNat_two_centralBinom]
  exact pow_succ_padicValNat_not_dvd (Nat.centralBinom_ne_zero n)

/-- **Powers of two.** When `n = 2^k`, the binary digit sum is `1`, so the central
binomial coefficient `C(2^{k+1}, 2^k)` is divisible by `2` exactly once:
`v₂(C(2·2^k, 2^k)) = 1`. -/
theorem padicValNat_two_centralBinom_pow_two (k : ℕ) :
    padicValNat 2 (Nat.centralBinom (2 ^ k)) = 1 := by
  rw [padicValNat_two_centralBinom]
  rw [show (2 : ℕ) ^ k = 2 ^ k * 1 by ring, Nat.digits_base_pow_mul one_lt_two one_pos]
  simp

/-- **All-ones case.** When `n = 2^k - 1` (binary representation `1…1`, `k` ones),
the digit sum is `k`, so `C(2n, n)` is divisible by exactly `2^k`:
`v₂(C(2n, n)) = k`. -/
theorem padicValNat_two_centralBinom_pred_pow_two (k : ℕ) :
    padicValNat 2 (Nat.centralBinom (2 ^ k - 1)) = k := by
  rw [padicValNat_two_centralBinom]
  -- reduces to s₂(2^k - 1) = k : the binary representation `1…1` has k ones
  induction k with
  | zero => simp
  | succ m ih =>
    have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    have hpos : 0 < (2 : ℕ) ^ m := by positivity
    have hstep : (2 : ℕ) ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by omega
    rw [hstep, Nat.digits_def' one_lt_two (by omega)]
    have e2 : (2 * (2 ^ m - 1) + 1) % 2 = 1 := by omega
    have e3 : (2 * (2 ^ m - 1) + 1) / 2 = 2 ^ m - 1 := by omega
    rw [e2, e3]
    simp only [List.sum_cons]
    rw [ih]
    omega

/-! ### Worked numeric witnesses (0-axiom)

Concrete `centralBinom` values are evaluated by kernel `decide` (`Nat.choose` is
structurally recursive).  The matching 2-adic valuations are read off from the
closed-form theorems above. -/

/-- `C(6, 3) = 20 = 2² · 5`, and `3 = 11₂` has `s₂(3) = 2`. -/
example : Nat.centralBinom 3 = 20 := by decide
example : padicValNat 2 (Nat.centralBinom 3) = 2 := by
  simpa using padicValNat_two_centralBinom_pred_pow_two 2

/-- `C(8, 4) = 70 = 2 · 35`, and `4 = 100₂` is a power of two: `s₂(4) = 1`. -/
example : Nat.centralBinom 4 = 70 := by decide
example : padicValNat 2 (Nat.centralBinom 4) = 1 := by
  simpa using padicValNat_two_centralBinom_pow_two 2

/-- `C(10, 5) = 252 = 2² · 63` (`5 = 101₂`, so `s₂(5) = 2`). -/
example : Nat.centralBinom 5 = 252 := by decide

/-- `n = 7 = 111₂` has digit sum `3`, so `2³ = 8` divides `C(14, 7) = 3432 = 2³ · 429`. -/
example : padicValNat 2 (Nat.centralBinom 7) = 3 := by
  simpa using padicValNat_two_centralBinom_pred_pow_two 3

example : Nat.centralBinom 7 = 3432 := by decide

end KummerCentralBinom
