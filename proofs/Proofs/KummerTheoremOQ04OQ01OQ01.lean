import Mathlib

/-
# When is the Central Binomial Coefficient `C(2n, n)` Divisible by `4` Exactly?

## The Open Question

The parent result (`KummerTheoremOQ04OQ01`) characterises the *minimal* case of the
2-adic valuation of the central binomial coefficient:

$$\nu_2\binom{2n}{n} \;=\; s_2(n) \;=\; 1 \iff n = 2^k,$$

where `s₂(n) = (Nat.digits 2 n).sum` is the binary digit sum (popcount) of `n`. Its
first listed open question asks for the **next level set of popcount**:

> Characterise the `n` with `v₂(C(2n,n)) = 2` (exactly two 1-bits): is there a clean
> closed description of this level set of popcount?

## Answer: exactly the sums of two distinct powers of two

$$\nu_2\binom{2n}{n} = 2 \iff \exists\, a > b,\; n = 2^a + 2^b.$$

### Why this is true

By the parent valuation formula `v₂(C(2n,n)) = s₂(n)`, the statement reduces to the
purely number-theoretic popcount characterisation

$$s_2(n) = 2 \iff \exists\, a > b,\; n = 2^a + 2^b,$$

i.e. `n` has exactly two `1`-bits, in positions `a > b`.

* **Forward** (`s₂(n) = 2 ⟹ two distinct powers`): strong induction peeling the lowest
  bit, `s₂(n) = (n % 2) + s₂(n / 2)`. If `n` is even the two bits live in `n/2`
  (shift both up by one); if `n` is odd the lowest bit is one of the two, so
  `s₂(n/2) = 1`, hence `n/2` is a *single* power of two — exactly the parent's
  `popcount = 1` lemma reused as a black box, giving `n = 2^{k+1} + 2^0`.
* **Converse**: factor `2^a + 2^b = 2^b·(2^{a-b}+1)` and use
  `Nat.digits_base_pow_mul` to strip the `b` trailing zero bits, reducing to
  `s₂(2^c + 1) = 2` for `c ≥ 1`, which is `1` (lowest bit) plus `s₂(2^{c-1}) = 1`.

This is a genuinely new level-set description: the parent stops at `popcount = 1`, and
Mathlib has no `popcount = 2` characterisation.

## Results in this file (original content, 0 axioms / 0 sorries)

* `sum_digits_two_two_pow_add_one` : `s₂(2^c + 1) = 2` for `c ≥ 1`
* `sum_digits_two_eq_two_iff`      : `s₂(n) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`  ← core
* `padicValNat_two_centralBinom_eq_two_iff`
                                   : `v₂(C(2n,n)) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`
* `four_exactDvd_centralBinom_of_two_bits`
                                   : two distinct bits ⟹ `4 ∣ C(2n,n) ∧ ¬ 8 ∣ C(2n,n)`
* worked numeric witnesses (`n = 3,5,6` give `v₂ = 2`; `n = 7` (popcount 3) does not).
-/

namespace KummerCentralBinomTwoBits

open Nat

/-- **Doubling-invariance of the binary digit sum.** `s₂(2n) = s₂(n)` (multiplying by
the base prepends a `0` digit). -/
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

/-- **Digit sum of a pure power of two is one.** `s₂(2^k) = 1`. -/
theorem sum_digits_two_pow (k : ℕ) :
    (Nat.digits 2 (2 ^ k)).sum = 1 := by
  rw [show (2 : ℕ) ^ k = 2 ^ k * 1 by ring, Nat.digits_base_pow_mul one_lt_two one_pos]
  simp

/-- **`s₂(n) = 1 ⟹ n` is a power of two** (parent `popcount = 1` lemma, re-derived to
keep this file self-contained). Strong induction peeling the lowest bit. -/
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

/-- **The 2-adic valuation of the central binomial coefficient is the binary digit
sum** (parent headline, re-derived self-contained): `v₂(C(2n, n)) = s₂(n)`. -/
theorem padicValNat_two_centralBinom (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : n ≤ 2 * n := by omega
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := n) (n := 2 * n) h
  have e1 : (2 : ℕ) * n - n = n := by omega
  rw [e1, sum_digits_two_mul] at key
  rw [Nat.centralBinom_eq_two_mul_choose]
  omega

/-- **Digit sum of `2^c + 1` (for `c ≥ 1`) is two.** The lowest bit is `1`, and the
remaining `2^{c-1}` contributes its single bit. -/
theorem sum_digits_two_two_pow_add_one {c : ℕ} (hc : 0 < c) :
    (Nat.digits 2 (2 ^ c + 1)).sum = 2 := by
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  have hpos : 0 < 2 ^ (d + 1) + 1 := by positivity
  rw [Nat.digits_def' one_lt_two hpos, List.sum_cons]
  -- lowest bit: (2^{d+1}+1) % 2 = 1 ; remaining: (2^{d+1}+1) / 2 = 2^d
  have hpow : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  have hmod : (2 ^ (d + 1) + 1) % 2 = 1 := by rw [hpow]; omega
  have hdiv : (2 ^ (d + 1) + 1) / 2 = 2 ^ d := by rw [hpow]; omega
  rw [hmod, hdiv, sum_digits_two_pow]

/-- **Forward direction.** If `s₂(n) = 2` then `n` is a sum of two distinct powers of
two: `∃ a b, b < a ∧ n = 2^a + 2^b`. Strong induction peeling the lowest bit. -/
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
    · -- n even: both bits live in n/2; shift up by one
      have h0 : n % 2 = 0 := Nat.even_iff.mp he
      rw [h0, Nat.zero_add] at h
      obtain ⟨a, b, hba, hab⟩ := ih (n / 2) hhalf h
      refine ⟨a + 1, b + 1, by omega, ?_⟩
      have he2 : n = 2 * (n / 2) := by omega
      rw [he2, hab, pow_succ, pow_succ]; ring
    · -- n odd: lowest bit is one of the two, so n/2 has a single bit (a power of two)
      have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [h1] at h
      have hsum : (Nat.digits 2 (n / 2)).sum = 1 := by omega
      obtain ⟨k, hk⟩ := sum_digits_two_eq_one_imp (n / 2) hsum
      refine ⟨k + 1, 0, by omega, ?_⟩
      have he2 : n = 2 * (n / 2) + 1 := by omega
      rw [he2, hk, pow_succ, pow_zero]; ring

/-- **Core characterisation: the binary digit sum equals two exactly for sums of two
distinct powers of two.** `s₂(n) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`.
(Not available in Mathlib.) -/
theorem sum_digits_two_eq_two_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 2 ↔ ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
  constructor
  · exact sum_digits_two_eq_two_imp n
  · rintro ⟨a, b, hba, rfl⟩
    obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    have hc : 0 < c := by omega
    have hfact : (2 : ℕ) ^ (b + c) + 2 ^ b = 2 ^ b * (2 ^ c + 1) := by
      rw [pow_add]; ring
    rw [hfact, Nat.digits_base_pow_mul one_lt_two (by positivity), List.sum_append]
    simp only [List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
    exact sum_digits_two_two_pow_add_one hc

/-- **Headline characterisation.** The central binomial coefficient `C(2n, n)` is
divisible by `2` *exactly twice* iff `n` is a sum of two distinct powers of two:
`v₂(C(2n, n)) = 2 ↔ ∃ a b, b < a ∧ n = 2^a + 2^b`. -/
theorem padicValNat_two_centralBinom_eq_two_iff (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = 2 ↔ ∃ a b, b < a ∧ n = 2 ^ a + 2 ^ b := by
  rw [padicValNat_two_centralBinom]
  exact sum_digits_two_eq_two_iff n

/-- **Sharp divisibility at a two-bit `n`.** When `n = 2^a + 2^b` with `b < a`, the
central binomial coefficient is divisible by `4` but not by `8`:
`4 ∣ C(2n,n)` and `¬ 8 ∣ C(2n,n)`. -/
theorem four_exactDvd_centralBinom_of_two_bits {a b : ℕ} (hba : b < a) :
    4 ∣ Nat.centralBinom (2 ^ a + 2 ^ b) ∧ ¬ (8 ∣ Nat.centralBinom (2 ^ a + 2 ^ b)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 (Nat.centralBinom (2 ^ a + 2 ^ b)) = 2 :=
    (padicValNat_two_centralBinom_eq_two_iff _).mpr ⟨a, b, hba, rfl⟩
  refine ⟨?_, ?_⟩
  · have hd : (2 : ℕ) ^ padicValNat 2 (Nat.centralBinom (2 ^ a + 2 ^ b)) ∣
        Nat.centralBinom (2 ^ a + 2 ^ b) := pow_padicValNat_dvd
    rw [hv] at hd
    rwa [show (4 : ℕ) = 2 ^ 2 by norm_num]
  · intro h8
    have h8' : (2 : ℕ) ^ 3 ∣ Nat.centralBinom (2 ^ a + 2 ^ b) := by
      rwa [show (8 : ℕ) = 2 ^ 3 by norm_num] at h8
    have hle := (padicValNat_dvd_iff_le (Nat.centralBinom_ne_zero _)).mp h8'
    rw [hv] at hle; omega

/-! ### Worked numeric witnesses (0-axiom)

Concrete `centralBinom` values are evaluated by kernel `decide`; valuations are read
off from the characterisation above. -/

/-- `n = 3 = 2^1 + 2^0`: `C(6,3) = 20 = 2^2 · 5`, so `v₂ = 2`. -/
example : Nat.centralBinom 3 = 20 := by decide
example : padicValNat 2 (Nat.centralBinom 3) = 2 :=
  (padicValNat_two_centralBinom_eq_two_iff 3).mpr ⟨1, 0, by norm_num, by norm_num⟩

/-- `n = 5 = 2^2 + 2^0`: `C(10,5) = 252 = 2^2 · 63`, so `v₂ = 2`. -/
example : Nat.centralBinom 5 = 252 := by decide
example : padicValNat 2 (Nat.centralBinom 5) = 2 :=
  (padicValNat_two_centralBinom_eq_two_iff 5).mpr ⟨2, 0, by norm_num, by norm_num⟩

/-- `n = 6 = 2^2 + 2^1`: `C(12,6) = 924 = 2^2 · 231`, so `v₂ = 2`. -/
example : Nat.centralBinom 6 = 924 := by decide
example : padicValNat 2 (Nat.centralBinom 6) = 2 :=
  (padicValNat_two_centralBinom_eq_two_iff 6).mpr ⟨2, 1, by norm_num, by norm_num⟩

/-- `n = 7 = 111₂` has popcount `3`, so `v₂(C(14,7)) ≠ 2` (indeed `C(14,7) = 3432 =
2^3 · 429`). -/
example : Nat.centralBinom 7 = 3432 := by decide
example : padicValNat 2 (Nat.centralBinom 7) ≠ 2 := by
  rw [ne_eq, padicValNat_two_centralBinom_eq_two_iff]
  rintro ⟨a, b, hba, hk⟩
  -- 2^a + 2^b = 7 is impossible: a ≤ 2 forces small cases, none equal 7
  have ha : a ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have : (2 : ℕ) ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hcon
    have hb : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
    omega
  interval_cases a <;> interval_cases b <;> omega

end KummerCentralBinomTwoBits
