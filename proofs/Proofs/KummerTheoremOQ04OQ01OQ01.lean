import Mathlib
import Proofs.KummerTheoremOQ04OQ01

/-
# Central binomial coefficients divisible by exactly four ⟺ `n` has two `1`-bits

By Kummer's theorem the exact power of two dividing the central binomial
coefficient `C(2n, n)` equals the binary digit sum (popcount) `s₂(n)`
(the parent file `KummerTheoremOQ04OQ01` re-derives this as
`padicValNat_two_centralBinom : v₂(C(2n,n)) = s₂(n)`, and characterises the
popcount-`1` level: `s₂(n) = 1 ↔ ∃ k, n = 2^k`).

This file advances the correspondence one level, to popcount `2`.  The
combinatorial heart is a clean classification of the naturals whose binary
digit sum equals `2`:

  `s₂(n) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`

i.e. the numbers with exactly two `1`-bits.  Transporting it through the parent
valuation identity gives

  `v₂(C(2n, n)) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`

and the exact-divisibility form

  `4 ∣ C(2n, n) ∧ ¬ 8 ∣ C(2n, n) ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`.

Mathlib provides `Nat.digits`, the digit recursion `Nat.digits_def'`, and
`padicValNat_dvd_iff_le` (`p^k ∣ a ↔ k ≤ v_p a` for `a ≠ 0`), but it has no
`popcount = 2 ↔ two distinct powers of two`.  The proof is fully finite and
`0`-axiom: the forward classification is a strong induction peeling the lowest
bit (even branch recurses, odd branch lands on the parent's popcount-`1`
lemma), and the converse computes the digit sum of `2^b · (2^m + 1)` via
doubling-invariance.
-/

namespace KummerCentralBinomTwoBits

open Nat
open KummerCentralBinomPowerTwo

/-- **Doubling a power of two leaves the binary digit sum unchanged.**
`s₂(2^c · x) = s₂(x)`: each multiplication by `2` prepends a zero digit. -/
theorem sum_digits_two_pow_mul (c x : ℕ) :
    (Nat.digits 2 (2 ^ c * x)).sum = (Nat.digits 2 x).sum := by
  induction c with
  | zero => simp
  | succ d ih =>
    have hrw : 2 ^ (d + 1) * x = 2 * (2 ^ d * x) := by ring
    rw [hrw, sum_digits_two_mul, ih]

/-- **Digit sum of `2^(m+1) + 1` is two.** The number `2^(m+1)+1` is odd with a
single high bit, so its binary expansion is `1 0…0 1`: digit sum `1 + s₂(2^m) = 2`. -/
theorem sum_digits_two_pow_succ_add_one (m : ℕ) :
    (Nat.digits 2 (2 ^ (m + 1) + 1)).sum = 2 := by
  have hpos : 0 < 2 ^ (m + 1) + 1 := by positivity
  rw [Nat.digits_def' one_lt_two hpos, List.sum_cons]
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hmod : (2 ^ (m + 1) + 1) % 2 = 1 := by omega
  have hdiv : (2 ^ (m + 1) + 1) / 2 = 2 ^ m := by omega
  rw [hmod, hdiv, sum_digits_two_pow]

/-- **Forward direction.** If the binary digit sum of `n` is `2`, then `n` is a sum
of two distinct powers of two.  Strong induction peeling the lowest bit
`s₂(n) = (n % 2) + s₂(n / 2)`: the even branch recurses on `n / 2`, while the odd
branch reduces `s₂(n/2) = 1` to the parent's popcount-one lemma. -/
theorem sum_digits_two_eq_two_imp (n : ℕ) :
    (Nat.digits 2 n).sum = 2 → ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
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
    · -- `n` even: lowest bit `0`, so `s₂(n/2) = 2`; recurse and double the exponents.
      have h0 : n % 2 = 0 := Nat.even_iff.mp he
      rw [h0, Nat.zero_add] at h
      obtain ⟨a, b, hab, hres⟩ := ih (n / 2) hhalf h
      refine ⟨a + 1, b + 1, by omega, ?_⟩
      have he2 : n = 2 * (n / 2) := by omega
      rw [he2, hres]; ring
    · -- `n` odd: lowest bit `1`, so `s₂(n/2) = 1`, hence `n/2 = 2^k` (parent lemma).
      have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [h1] at h
      have hk : (Nat.digits 2 (n / 2)).sum = 1 := by omega
      obtain ⟨k, hkk⟩ := sum_digits_two_eq_one_imp (n / 2) hk
      refine ⟨k + 1, 0, by omega, ?_⟩
      have he2 : n = 2 * (n / 2) + 1 := by omega
      rw [he2, hkk]; ring

/-- **Converse direction.** A sum of two distinct powers of two has binary digit
sum `2`.  Factor `2^a + 2^b = 2^b · (2^(a-b) + 1)`, strip the `2^b` factor by
doubling-invariance, and evaluate `s₂(2^(a-b) + 1) = 2`. -/
theorem sum_digits_two_eq_two_of (a b : ℕ) (hab : b < a) :
    (Nat.digits 2 (2 ^ a + 2 ^ b)).sum = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = b + (m + 1) := ⟨a - b - 1, by omega⟩
  have hfac : 2 ^ (b + (m + 1)) + 2 ^ b = 2 ^ b * (2 ^ (m + 1) + 1) := by
    rw [pow_add]; ring
  rw [hfac, sum_digits_two_pow_mul, sum_digits_two_pow_succ_add_one]

/-- **The binary digit sum equals two exactly for the two-bit numbers.**
`s₂(n) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`.  (Not available in Mathlib.) -/
theorem sum_digits_two_eq_two_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 2 ↔ ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
  constructor
  · exact sum_digits_two_eq_two_imp n
  · rintro ⟨a, b, hab, rfl⟩
    exact sum_digits_two_eq_two_of a b hab

/-- **Headline valuation characterisation.** The central binomial coefficient
`C(2n, n)` has `2`-adic valuation exactly `2` iff `n` has precisely two `1`-bits:
`v₂(C(2n, n)) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`. -/
theorem padicValNat_two_centralBinom_eq_two_iff (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = 2 ↔ ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
  rw [padicValNat_two_centralBinom]
  exact sum_digits_two_eq_two_iff n

/-- **Exact-divisibility bridge.** For `m > 0`, having `2`-adic valuation exactly `2`
is the same as `4 ∣ m` but `8 ∤ m`, since `4 = 2²` and `8 = 2³`. -/
theorem exactDvd_four_iff_padicValNat_two {m : ℕ} (hm : 0 < m) :
    (4 ∣ m ∧ ¬ (8 ∣ m)) ↔ padicValNat 2 m = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h4, h8, padicValNat_dvd_iff_le hm.ne', padicValNat_dvd_iff_le hm.ne']
  omega

/-- **Headline exact-divisibility form.** `C(2n, n)` is divisible by `4` but not by
`8` exactly when `n` is a sum of two distinct powers of two. -/
theorem four_exactDvd_centralBinom_iff (n : ℕ) :
    (4 ∣ Nat.centralBinom n ∧ ¬ (8 ∣ Nat.centralBinom n)) ↔
      ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
  rw [exactDvd_four_iff_padicValNat_two (Nat.centralBinom_pos n)]
  exact padicValNat_two_centralBinom_eq_two_iff n

/-! ### Sanity checks (anonymous examples; not part of the API) -/

/-- `n = 3 = 11₂ = 2¹ + 2⁰`: two bits, so `v₂(C(6,3)) = v₂(20) = 2`. -/
example : padicValNat 2 (Nat.centralBinom 3) = 2 :=
  (padicValNat_two_centralBinom_eq_two_iff 3).mpr ⟨1, 0, by omega, by norm_num⟩

/-- `n = 6 = 110₂ = 2² + 2¹`: two bits, so `C(12,6) = 924` is `4 ∣ · ∧ ¬ 8 ∣ ·`. -/
example : 4 ∣ Nat.centralBinom 6 ∧ ¬ (8 ∣ Nat.centralBinom 6) :=
  (four_exactDvd_centralBinom_iff 6).mpr ⟨2, 1, by omega, by norm_num⟩

/-- `n = 7 = 111₂` has three bits, so `v₂(C(14,7)) ≠ 2`: `7` is not a sum of two
distinct powers of two. -/
example : padicValNat 2 (Nat.centralBinom 7) ≠ 2 := by
  rw [ne_eq, padicValNat_two_centralBinom_eq_two_iff]
  rintro ⟨a, b, hab, hc⟩
  have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have ha1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have haa : a ≤ 2 := by
    by_contra h
    have h3 : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h3; omega
  interval_cases a <;> interval_cases b <;> simp_all

end KummerCentralBinomTwoBits
