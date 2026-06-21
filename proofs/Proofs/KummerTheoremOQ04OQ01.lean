import Mathlib

/-
# When is the Central Binomial Coefficient `C(2n, n)` Divisible by 2 Exactly Once?

## The Open Question

The parent result (`KummerTheoremOQ04`) computes the 2-adic valuation of the central
binomial coefficient as the binary digit sum:

$$\nu_2\binom{2n}{n} \;=\; s_2(n),$$

where `s₂(n) = (Nat.digits 2 n).sum` is the number of `1`-bits of `n` (its popcount).

A natural sharp follow-up asks for the *characterisation of the extreme case*: for
which `n` is `C(2n, n)` divisible by `2` **exactly once**, i.e. `v₂(C(2n,n)) = 1`?

## Answer: exactly when `n` is a power of two

$$\nu_2\binom{2n}{n} = 1 \iff \exists k,\; n = 2^k.$$

### Why this is true

By the parent valuation formula this is equivalent to `s₂(n) = 1`, and the binary
digit sum of a natural number equals `1` exactly when its binary expansion is a single
`1` followed by zeros — that is, exactly when `n` is a power of `2`.

The substantive new content here is the number-theoretic lemma

* `sum_digits_two_eq_one_iff` : `s₂(n) = 1 ↔ ∃ k, n = 2^k`,

which **Mathlib does not provide** (there is no `popcount = 1 ↔ power of two`
characterisation in `Mathlib.Data.Nat.Digits`). The forward direction is a strong
induction peeling the lowest bit; the converse reuses the digit sum of a pure power.

## What Mathlib / the parent already have (reused here, kept self-contained)

* `Nat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits` — Kummer in digit-sum form;
* `Nat.digits_base_mul`, `Nat.digits_def'`, `Nat.digits_base_pow_mul` — digit recursion;
* the headline `v₂(C(2n,n)) = s₂(n)` is re-derived locally (≈10 lines) so this file
  stands alone.

## Results in this file (original content, 0 axioms / 0 sorries)

* `sum_digits_two_eq_one_iff`           : `s₂(n) = 1 ↔ ∃ k, n = 2^k`  ← the new lemma
* `padicValNat_two_centralBinom_eq_one_iff`
                                        : `v₂(C(2n,n)) = 1 ↔ ∃ k, n = 2^k`  ← headline
* `two_exactDvd_centralBinom_of_pow_two`: `n = 2^k ⟹ 2 ∣ C(2n,n) ∧ ¬ 4 ∣ C(2n,n)`
* worked numeric witnesses (`C(2,1)=2`, `C(8,4)=70`, `n=6` is not a power of two …).
-/

namespace KummerCentralBinomPowerTwo

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
sum** (parent headline, re-derived to keep this file self-contained):
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

/-- **Digit sum of a pure power of two is one.** `s₂(2^k) = 1`: the binary expansion
of `2^k` is `1` preceded by `k` zeros. -/
theorem sum_digits_two_pow (k : ℕ) :
    (Nat.digits 2 (2 ^ k)).sum = 1 := by
  rw [show (2 : ℕ) ^ k = 2 ^ k * 1 by ring, Nat.digits_base_pow_mul one_lt_two one_pos]
  simp

/-- **Forward direction of the characterisation.** If the binary digit sum of `n` is
`1`, then `n` is a power of two. Strong induction, peeling the lowest bit:
`s₂(n) = (n % 2) + s₂(n / 2)`. -/
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
    -- h : n % 2 + (Nat.digits 2 (n / 2)).sum = 1
    have hhalf : n / 2 < n := Nat.div_lt_self hn one_lt_two
    rcases Nat.even_or_odd n with he | ho
    · -- n even: lowest bit is 0, so s₂(n/2) = 1
      have h0 : n % 2 = 0 := Nat.even_iff.mp he
      rw [h0, Nat.zero_add] at h
      obtain ⟨j, hj⟩ := ih (n / 2) hhalf h
      refine ⟨j + 1, ?_⟩
      have he2 : n = 2 * (n / 2) := by omega
      rw [he2, hj]; ring
    · -- n odd: lowest bit is 1, so s₂(n/2) = 0, forcing n/2 = 0 and n = 1 = 2^0
      have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
      rw [h1] at h
      have hz : (Nat.digits 2 (n / 2)).sum = 0 := by omega
      have hz2 : n / 2 = 0 := by
        by_contra hne
        have := sum_digits_two_pos (Nat.pos_of_ne_zero hne)
        omega
      exact ⟨0, by rw [pow_zero]; omega⟩

/-- **The binary digit sum equals one exactly for powers of two.**
`s₂(n) = 1 ↔ ∃ k, n = 2^k`. (Not available in Mathlib.) -/
theorem sum_digits_two_eq_one_iff (n : ℕ) :
    (Nat.digits 2 n).sum = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · exact sum_digits_two_eq_one_imp n
  · rintro ⟨k, rfl⟩
    exact sum_digits_two_pow k

/-- **Headline characterisation.** The central binomial coefficient `C(2n, n)` is
divisible by `2` exactly once iff `n` is a power of two:
`v₂(C(2n, n)) = 1 ↔ ∃ k, n = 2^k`. -/
theorem padicValNat_two_centralBinom_eq_one_iff (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = 1 ↔ ∃ k, n = 2 ^ k := by
  rw [padicValNat_two_centralBinom]
  exact sum_digits_two_eq_one_iff n

/-- **Sharp divisibility at a power of two.** When `n = 2^k`, the central binomial
coefficient is divisible by `2` but not by `4`: `2 ∣ C(2n,n)` and `¬ 4 ∣ C(2n,n)`. -/
theorem two_exactDvd_centralBinom_of_pow_two (k : ℕ) :
    2 ∣ Nat.centralBinom (2 ^ k) ∧ ¬ (4 ∣ Nat.centralBinom (2 ^ k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 (Nat.centralBinom (2 ^ k)) = 1 := by
    rw [padicValNat_two_centralBinom, sum_digits_two_pow]
  refine ⟨?_, ?_⟩
  · have hd : (2 : ℕ) ^ padicValNat 2 (Nat.centralBinom (2 ^ k)) ∣
        Nat.centralBinom (2 ^ k) := pow_padicValNat_dvd
    rwa [hv, pow_one] at hd
  · intro h4
    have h4' : (2 : ℕ) ^ 2 ∣ Nat.centralBinom (2 ^ k) := by
      rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at h4
    have hle := (padicValNat_dvd_iff_le (Nat.centralBinom_ne_zero _)).mp h4'
    rw [hv] at hle; omega

/-! ### Worked numeric witnesses (0-axiom)

Concrete `centralBinom` values are evaluated by kernel `decide`; valuations are read
off from the characterisation above. -/

/-- `n = 1 = 2^0`: `C(2,1) = 2`, divisible by `2` exactly once. -/
example : Nat.centralBinom 1 = 2 := by decide
example : padicValNat 2 (Nat.centralBinom 1) = 1 :=
  (padicValNat_two_centralBinom_eq_one_iff 1).mpr ⟨0, rfl⟩

/-- `n = 4 = 2^2`: `C(8,4) = 70 = 2 · 35`, so `v₂ = 1`. -/
example : Nat.centralBinom 4 = 70 := by decide
example : padicValNat 2 (Nat.centralBinom 4) = 1 :=
  (padicValNat_two_centralBinom_eq_one_iff 4).mpr ⟨2, rfl⟩

/-- `n = 8 = 2^3`: a power of two, so `v₂(C(16,8)) = 1`. -/
example : padicValNat 2 (Nat.centralBinom 8) = 1 :=
  (padicValNat_two_centralBinom_eq_one_iff 8).mpr ⟨3, rfl⟩

/-- `n = 6 = 110₂` is **not** a power of two (`s₂(6) = 2`), so `v₂(C(12,6)) ≠ 1`
(indeed `C(12,6) = 924 = 2² · 231`). -/
example : Nat.centralBinom 6 = 924 := by decide
example : padicValNat 2 (Nat.centralBinom 6) ≠ 1 := by
  rw [ne_eq, padicValNat_two_centralBinom_eq_one_iff]
  rintro ⟨k, hk⟩
  have hk6 : (2 : ℕ) ^ k = 6 := hk.symm
  have hk3 : k < 3 := by
    by_contra hcon
    push_neg at hcon
    have : (2 : ℕ) ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  interval_cases k <;> norm_num at hk6

end KummerCentralBinomPowerTwo
