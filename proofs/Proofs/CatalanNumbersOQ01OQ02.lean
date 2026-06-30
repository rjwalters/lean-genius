import Mathlib

/-!
# Catalan OQ-01-OQ-02: The 2-adic Valuation of the Catalan Numbers

The Catalan numbers `Cₙ = catalan n` satisfy `(n+1)·Cₙ = C(2n,n)` (Mathlib's
`succ_mul_catalan_eq_centralBinom`).  Combining this with the base-2 case of
Kummer's theorem — `v₂(C(2n,n)) = s₂(n)`, where `s₂` is the binary digit sum — and
with **Legendre's formula** `v₂(m!) = m − s₂(m)`, we obtain a complete description
of the 2-adic valuation of the Catalan numbers:

* `padicValNat_two_catalan`    : `v₂(Cₙ) = s₂(n) − v₂(n+1)`
* `padicValNat_two_catalan_eq` : `v₂(Cₙ) = s₂(n+1) − 1`
* `odd_catalan_iff`            : `Cₙ` is odd ⟺ `n + 1` is a power of two
                                  (equivalently `n = 2ᵏ − 1`: `Cₙ` is odd exactly at
                                  the indices `0, 1, 3, 7, 15, …`).

The **carry identity** `s₂(n) + 1 = s₂(n+1) + v₂(n+1)` linking the two valuation
formulas is itself derived from Legendre's formula applied to `n!` and
`(n+1)! = (n+1)·n!`, with **no manual digit induction** — the only digit recursion
in the file is for the elementary `s₂ = 1 ⟺ power of two` characterisation.

This sits alongside the central-binomial entries (`kummer-theorem-oq-04`) and the
sibling Catalan reflection form (`catalan-numbers-oq-01-oq-01`); it is the first
gallery entry on the *arithmetic* (divisibility / parity) structure of the Catalan
numbers.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat

namespace CatalanTwoAdic

/-! ### Elementary binary digit-sum lemmas -/

/-- Doubling a number prepends a `0` binary digit, so `s₂(2n) = s₂(n)`. -/
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

/-- The binary digit sum of a power of two is `1`. -/
theorem sum_digits_two_pow (k : ℕ) : (Nat.digits 2 (2 ^ k)).sum = 1 := by
  rw [show (2 : ℕ) ^ k = 2 ^ k * 1 by ring, Nat.digits_base_pow_mul one_lt_two one_pos]
  simp

/-- If the binary digit sum of `n` is `1` then `n` is a power of two. -/
theorem sum_digits_two_eq_one_imp (n : ℕ) :
    (Nat.digits 2 n).sum = 1 → ∃ k, n = 2 ^ k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp at h
      · exact hp
    rw [Nat.digits_def' one_lt_two hn, List.sum_cons] at h
    have hhalf : n / 2 < n := Nat.div_lt_self hn one_lt_two
    rcases Nat.even_or_odd n with he | ho
    · have h0 : n % 2 = 0 := Nat.even_iff.mp he
      rw [h0, Nat.zero_add] at h
      obtain ⟨j, hj⟩ := ih (n / 2) hhalf h
      refine ⟨j + 1, ?_⟩
      have he2 : n = 2 * (n / 2) := by omega
      rw [he2, hj]; ring
    · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [h1] at h
      have hz : (Nat.digits 2 (n / 2)).sum = 0 := by omega
      have hz2 : n / 2 = 0 := by
        by_contra hne
        have := sum_digits_two_pos (Nat.pos_of_ne_zero hne)
        omega
      exact ⟨0, by rw [pow_zero]; omega⟩

/-- **The binary digit sum equals one exactly for powers of two.** `s₂(n) = 1 ↔ ∃ k, n = 2^k`. -/
theorem sum_digits_two_eq_one_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k :=
  ⟨sum_digits_two_eq_one_imp n, by rintro ⟨k, rfl⟩; exact sum_digits_two_pow k⟩

/-! ### Legendre's formula and the central binomial valuation -/

/-- **Legendre's formula, base `2`.** `v₂(m!) = m − s₂(m)`. -/
theorem padicValNat_two_factorial (m : ℕ) :
    padicValNat 2 (m !) = m - (Nat.digits 2 m).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  rw [show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at h
  exact h

/-- **Base-2 Kummer (central binomial).** `v₂(C(2n, n)) = s₂(n)`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n)
    (by omega)
  rw [show (2 : ℕ) * n - n = n by omega, sum_digits_two_mul,
      show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at key
  rw [Nat.centralBinom_eq_two_mul_choose]
  omega

/-- **Carry identity** (no digit induction): incrementing `n` changes the binary
digit sum by `1 − v₂(n+1)`, i.e. `s₂(n) + 1 = s₂(n+1) + v₂(n+1)`.  Proved purely
from Legendre's formula applied to `n!` and `(n+1)! = (n+1)·n!`. -/
theorem sum_digits_two_succ (n : ℕ) :
    (Nat.digits 2 n).sum + 1 = (Nat.digits 2 (n + 1)).sum + padicValNat 2 (n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := padicValNat_two_factorial n
  have hn1 := padicValNat_two_factorial (n + 1)
  have hmul : padicValNat 2 ((n + 1)!) = padicValNat 2 (n + 1) + padicValNat 2 (n !) := by
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]
  have hb := Nat.digit_sum_le 2 n
  have hb1 := Nat.digit_sum_le 2 (n + 1)
  omega

/-! ### The 2-adic valuation of the Catalan numbers -/

/-- `catalan n ≠ 0`. -/
theorem catalan_ne_zero (n : ℕ) : catalan n ≠ 0 := by
  intro h
  have hmul := succ_mul_catalan_eq_centralBinom n
  rw [h, Nat.mul_zero] at hmul
  exact (Nat.centralBinom_pos n).ne' hmul.symm

/-- **The 2-adic valuation of the Catalan numbers.**
`v₂(Cₙ) = s₂(n) − v₂(n+1)`: the binary digit sum of `n` minus the 2-adic valuation
of `n+1`.  Immediate from `(n+1)·Cₙ = C(2n,n)` and `v₂(C(2n,n)) = s₂(n)`. -/
theorem padicValNat_two_catalan (n : ℕ) :
    padicValNat 2 (catalan n) = (Nat.digits 2 n).sum - padicValNat 2 (n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := succ_mul_catalan_eq_centralBinom n
  have hadd : padicValNat 2 (Nat.centralBinom n)
      = padicValNat 2 (n + 1) + padicValNat 2 (catalan n) := by
    rw [← hmul, padicValNat.mul (by omega) (catalan_ne_zero n)]
  rw [padicValNat_two_centralBinom] at hadd
  omega

/-- **Closed form via the successor digit sum.** `v₂(Cₙ) = s₂(n+1) − 1`. -/
theorem padicValNat_two_catalan_eq (n : ℕ) :
    padicValNat 2 (catalan n) = (Nat.digits 2 (n + 1)).sum - 1 := by
  have h1 := padicValNat_two_catalan n
  have h2 := sum_digits_two_succ n
  have hpos : 0 < (Nat.digits 2 (n + 1)).sum := sum_digits_two_pos (by omega)
  omega

/-- **Oddness of the Catalan numbers.** `Cₙ` is odd iff `n + 1` is a power of two,
equivalently `n = 2ᵏ − 1` (the indices `0, 1, 3, 7, 15, …`). -/
theorem odd_catalan_iff (n : ℕ) : Odd (catalan n) ↔ ∃ k, n + 1 = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ catalan n ↔ 1 ≤ padicValNat 2 (catalan n) := by
    rw [← padicValNat_dvd_iff_le (catalan_ne_zero n), pow_one]
  have hval := padicValNat_two_catalan_eq n
  have hpos : 0 < (Nat.digits 2 (n + 1)).sum := sum_digits_two_pos (by omega)
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd, hdvd, hval, ← sum_digits_two_eq_one_iff]
  omega

/-! ### Concrete examples -/

/-- `C₀ = 1`, `C₁ = 1`, `C₃ = 5`, `C₇ = 429` are odd (indices `2ᵏ − 1`). -/
example : Odd (catalan 0) := (odd_catalan_iff 0).mpr ⟨0, by norm_num⟩
example : Odd (catalan 1) := (odd_catalan_iff 1).mpr ⟨1, by norm_num⟩
example : Odd (catalan 3) := (odd_catalan_iff 3).mpr ⟨2, by norm_num⟩
example : Odd (catalan 7) := (odd_catalan_iff 7).mpr ⟨3, by norm_num⟩

/-- `C₂ = 2` and `C₄ = 14` are even (`3` and `5` are not powers of two). -/
example : ¬ Odd (catalan 2) := by rw [catalan_two]; decide

end CatalanTwoAdic
