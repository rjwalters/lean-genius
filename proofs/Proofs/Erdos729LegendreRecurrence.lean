/-
  Erdős Problem #729 — OQ-02 follow-up: 2-adic recurrences and the maximality
  characterization of `v₂(n!)`.

  Companion to `Erdos729Problem.lean` (the `p = 2` case `legendre_for_two`) and
  `Erdos729LegendreGeneral.lean` (the general identity for all primes). Those
  files establish Legendre's identity itself:

        v₂(n!) = n − s₂(n)            (s₂ = binary digit sum, number of 1-bits)

  This file develops the *consequences* of that identity that are NOT in Mathlib
  and not in the companion files: the **doubling recurrences** for the 2-adic
  valuation of factorials, and the **maximality characterization** describing
  exactly when `v₂(n!)` attains its largest possible value `n − 1`.

  ## Results

  * `binary_digit_sum_two_mul`     : `s₂(2n) = s₂(n)` — appending a `0` bit.
  * `binary_digit_sum_two_mul_add_one` : `s₂(2n+1) = s₂(n) + 1` — appending a `1` bit.
  * `legendre_two`                 : `v₂(n!) = n − s₂(n)` (re-derived locally, self-contained).
  * `v2_factorial_two_mul`         : `v₂((2n)!) = n + v₂(n!)`.
  * `v2_factorial_two_mul_add_one` : `v₂((2n+1)!) = n + v₂(n!)`.
  * `v2_factorial_eq_pred_iff`     : for `n ≥ 1`, `v₂(n!) = n − 1 ↔ s₂(n) = 1`.

  The doubling recurrence `v₂((2n)!) = n + v₂(n!)` is the clean arithmetic shadow
  of the fact that multiplying by `2` shifts the binary expansion left by one bit
  without changing its digit sum: the factorial of `2n` collects exactly `n`
  extra factors of `2` (one per even number `2, 4, …, 2n`) on top of the
  `v₂(n!)` it inherits.

  The maximality characterization records that `s₂(n) = 1`, i.e. `n` is a power
  of two, is *exactly* the condition for `v₂(n!)` to hit its ceiling `n − 1`
  (it is always `< n` for `n ≥ 1` by `padicValNat_factorial_lt_of_ne_zero`).
  We state the threshold in digit-sum form, which is self-contained; the
  equivalence `s₂(n) = 1 ↔ n is a power of two` is proved separately in the
  Kummer companion (`KummerTheoremOQ04OQ01.lean`) and is not reproved here.

  Bearer lemmas verified against the Mathlib pin `v4.26.0`:
  `sub_one_mul_padicValNat_factorial` (PadicVal/Basic.lean:587),
  `Nat.digits_def'` (Data/Nat/Digits/Defs.lean:115),
  `Nat.digit_sum_le` (Data/Nat/Digits/Defs.lean:432),
  `List.sum_cons`, `Nat.mul_mod_right`, `Nat.mul_div_cancel_left`.
-/

import Mathlib

namespace Erdos729Recurrence

open Nat

/-- The binary digit sum `s₂(n) = (Nat.digits 2 n).sum` (number of 1-bits). -/
noncomputable abbrev s₂ (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- **Doubling a number appends a `0` bit**, so the binary digit sum is
unchanged: `s₂(2n) = s₂(n)`. -/
theorem binary_digit_sum_two_mul (n : ℕ) : s₂ (2 * n) = s₂ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [s₂]
  · have h2n : 0 < 2 * n := by positivity
    have hmod : 2 * n % 2 = 0 := by simp [Nat.mul_mod_right]
    have hdiv : 2 * n / 2 = n := by
      rw [Nat.mul_div_cancel_left n (by norm_num)]
    simp only [s₂]
    rw [Nat.digits_def' (b := 2) (by norm_num) h2n, hmod, hdiv, List.sum_cons,
      Nat.zero_add]

/-- **`2n+1` appends a `1` bit**, so the binary digit sum gains one:
`s₂(2n+1) = s₂(n) + 1`. -/
theorem binary_digit_sum_two_mul_add_one (n : ℕ) : s₂ (2 * n + 1) = s₂ n + 1 := by
  have h2n : 0 < 2 * n + 1 := by positivity
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp only [s₂]
  rw [Nat.digits_def' (b := 2) (by norm_num) h2n, hmod, hdiv, List.sum_cons]
  omega

/-- **Legendre's identity for `p = 2`** (re-derived here so this file is
self-contained): `v₂(n!) = n − s₂(n)`. Obtained from Mathlib's multiplied form
`(2−1)·v₂(n!) = n − s₂(n)` by `one_mul`. -/
theorem legendre_two (n : ℕ) : padicValNat 2 n.factorial = n - s₂ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [show (2 - 1 : ℕ) = 1 from rfl, one_mul] at h
  simpa [s₂] using h

/-- **Doubling recurrence.** `v₂((2n)!) = n + v₂(n!)`.

The factorial of `2n` carries exactly `n` more factors of two than `n!`: one
from each of the `n` even numbers `2, 4, …, 2n`. Arithmetically this is the
Legendre identity together with `s₂(2n) = s₂(n)`. -/
theorem v2_factorial_two_mul (n : ℕ) :
    padicValNat 2 (2 * n).factorial = n + padicValNat 2 n.factorial := by
  have h2n := legendre_two (2 * n)
  have hn := legendre_two n
  have hdouble := binary_digit_sum_two_mul n
  have hle : s₂ n ≤ n := Nat.digit_sum_le 2 n
  rw [h2n, hdouble, hn]
  omega

/-- **Odd-step recurrence.** `v₂((2n+1)!) = n + v₂(n!)`.

Since `2n+1` is odd it contributes no new factor of two, so `(2n+1)!` has the
same 2-adic valuation as `(2n)!`. -/
theorem v2_factorial_two_mul_add_one (n : ℕ) :
    padicValNat 2 (2 * n + 1).factorial = n + padicValNat 2 n.factorial := by
  have h2n := legendre_two (2 * n + 1)
  have hn := legendre_two n
  have hodd := binary_digit_sum_two_mul_add_one n
  have hle : s₂ n ≤ n := Nat.digit_sum_le 2 n
  rw [h2n, hodd, hn]
  omega

/-- **Maximality characterization.** For `n ≥ 1`, the 2-adic valuation of `n!`
attains its maximum possible value `n − 1` exactly when the binary digit sum is
`1`, i.e. exactly when `n` is a power of two:

        v₂(n!) = n − 1   ↔   s₂(n) = 1.

(The valuation is always `< n` for `n ≥ 1`, so `n − 1` is the ceiling.) The
equivalence `s₂(n) = 1 ↔ ∃ k, n = 2^k` is proved in the Kummer companion. -/
theorem v2_factorial_eq_pred_iff (n : ℕ) (hn : 1 ≤ n) :
    padicValNat 2 n.factorial = n - 1 ↔ s₂ n = 1 := by
  have hL := legendre_two n
  have hle : s₂ n ≤ n := Nat.digit_sum_le 2 n
  rw [hL]
  omega

#check @v2_factorial_two_mul
#check @v2_factorial_two_mul_add_one
#check @v2_factorial_eq_pred_iff

end Erdos729Recurrence
