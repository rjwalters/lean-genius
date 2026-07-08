/-
  Erdős Problem #729 — OQ-02 follow-up: the elementary 2-adic digit-sum bound.

  Companion to `Erdos729Problem.lean` (the parent's `legendre_for_two`) and
  `Erdos729LegendreMultinomial.lean`.

  ## The question

  The parent entry (OQ-02) establishes Legendre's identity for `p = 2`,
  `v₂(n!) = n − s₂(n)` with `s₂(n) = (Nat.digits 2 n).sum` the binary digit sum.
  The parent's headline number-theoretic content — the Erdős (1968) constraint
  that `a! · b! ∣ n!` forces `a + b ≤ n + O(log n)` — is carried in the main file
  only by the DEEP axiom `erdos_1968_classical`. Yet the exact 2-adic *core* of
  that constraint is entirely elementary and needs no axiom:

        a! · b! ∣ n!   ⟹   v₂(a!) + v₂(b!) ≤ v₂(n!)
                       ⟹   (a − s₂ a) + (b − s₂ b) ≤ n − s₂ n
                       ⟹   a + b ≤ n + s₂(a) + s₂(b).                        (★)

  Inequality (★) is a correct, *sharp*, subtraction-free quantitative statement
  (no `O(·)` fudge): the excess `a + b − n` is bounded by the total number of
  1-bits in `a` and `b`. Since `s₂(m) ≤ ⌊log₂ m⌋ + 1`, (★) immediately yields the
  recognisable logarithmic shape `a + b ≤ n + (⌊log₂ a⌋ + 1) + (⌊log₂ b⌋ + 1)`.

  ## What this file proves (0 axioms / 0 sorries / 0 native_decide)

  * `v2_factorial`          — `v₂(n!) = n − s₂(n)` (Legendre at `p = 2`).
  * `v2_add_le_of_dvd`      — the valuation-monotonicity step
                              `v₂(a!) + v₂(b!) ≤ v₂(n!)` from `a!·b! ∣ n!`.
  * `erdos_two_adic_bound`  — the digit-sum bound (★), axiom-free.
  * `digitSum_two_le_log`   — `s₂(m) ≤ Nat.log 2 m + 1` (digit sum ≤ bit count).
  * `erdos_two_adic_bound_log` — the logarithmic corollary of (★).

  None of these are named Mathlib lemmas. Bearer lemmas (Mathlib pin `v4.26.0`):
  `sub_one_mul_padicValNat_factorial`, `Nat.factorization_prime_le_iff_dvd`,
  `Nat.factorization_mul`, `Nat.factorization_def`, `Nat.digit_sum_le`,
  `Nat.digits_len`, `Nat.digits_lt_base`, `List.sum_le_card_nsmul`.
-/

import Mathlib

namespace Erdos729DigitSum

open Nat

/-- **Legendre's identity at `p = 2`, subtraction form.**
`v₂(n!) = n − s₂(n)` with `s₂(n) = (Nat.digits 2 n).sum`. Discharged from
Mathlib's `sub_one_mul_padicValNat_factorial`, whose `p − 1` factor is `1`
at `p = 2`. -/
theorem v2_factorial (n : ℕ) :
    padicValNat 2 (n !) = n - (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [show (2 - 1 : ℕ) = 1 from rfl, one_mul] at h
  exact h

/-- **Valuation-monotonicity step.** If `a! · b! ∣ n!` then the 2-adic valuations
add up subordinately: `v₂(a!) + v₂(b!) ≤ v₂(n!)`. Proof via the factorization
order: `factorization` is monotone under divisibility and additive under products,
and agrees with `padicValNat` at the prime `2`. -/
theorem v2_add_le_of_dvd (n a b : ℕ) (h : a ! * b ! ∣ n !) :
    padicValNat 2 (a !) + padicValNat 2 (b !) ≤ padicValNat 2 (n !) := by
  have hab : a ! * b ! ≠ 0 :=
    mul_ne_zero (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)
  have hn : n ! ≠ 0 := Nat.factorial_ne_zero n
  have key := (Nat.factorization_prime_le_iff_dvd hab hn).mpr h 2 Nat.prime_two
  rw [Nat.factorization_mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b),
      Finsupp.add_apply,
      Nat.factorization_def (a !) Nat.prime_two,
      Nat.factorization_def (b !) Nat.prime_two,
      Nat.factorization_def (n !) Nat.prime_two] at key
  exact key

/-- **The 2-adic digit-sum bound (★), axiom-free.**
If `a! · b! ∣ n!` then `a + b ≤ n + s₂(a) + s₂(b)`, where `s₂(m)` is the number of
1-bits of `m`. The excess `a + b − n` never exceeds the total 1-bit count of the
two parts — the exact 2-adic content of Erdős's 1968 constraint, with no `O(·)`. -/
theorem erdos_two_adic_bound (n a b : ℕ) (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  have hv := v2_add_le_of_dvd n a b h
  rw [v2_factorial, v2_factorial, v2_factorial] at hv
  have ha := Nat.digit_sum_le 2 a
  have hb := Nat.digit_sum_le 2 b
  have hnn := Nat.digit_sum_le 2 n
  omega

/-- **Digit sum ≤ bit count.** For `m ≥ 1`, the binary digit sum is bounded by the
number of binary digits: `s₂(m) ≤ ⌊log₂ m⌋ + 1`. Each base-2 digit is `< 2`,
hence `≤ 1`, so the sum is at most the length, which is `Nat.log 2 m + 1`. -/
theorem digitSum_two_le_log (m : ℕ) (hm : m ≠ 0) :
    (Nat.digits 2 m).sum ≤ Nat.log 2 m + 1 := by
  have hlen : (Nat.digits 2 m).length = Nat.log 2 m + 1 :=
    Nat.digits_len 2 m (by norm_num) hm
  have hbound : (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length • 1 :=
    List.sum_le_card_nsmul (Nat.digits 2 m) 1 fun x hx => by
      have := Nat.digits_lt_base (by norm_num) hx
      omega
  have hsmul : (Nat.digits 2 m).length • (1 : ℕ) = (Nat.digits 2 m).length := by simp
  rw [hsmul] at hbound
  omega

/-- **Logarithmic corollary of (★).** If `a! · b! ∣ n!` with `a, b ≥ 1` then
`a + b ≤ n + (⌊log₂ a⌋ + 1) + (⌊log₂ b⌋ + 1)` — the recognisable `n + O(log n)`
shape of Erdős's bound, here with explicit constants and no axiom. -/
theorem erdos_two_adic_bound_log (n a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ! * b ! ∣ n !) :
    a + b ≤ n + (Nat.log 2 a + 1) + (Nat.log 2 b + 1) := by
  have hmain := erdos_two_adic_bound n a b h
  have hla := digitSum_two_le_log a ha
  have hlb := digitSum_two_le_log b hb
  omega

end Erdos729DigitSum
