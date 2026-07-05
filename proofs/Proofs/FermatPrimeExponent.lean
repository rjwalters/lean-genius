import Mathlib

/-
# Fermat Prime Exponents Are Powers of Two

## Open Question (mersenne-prime-exponent-oq-01)

A **Fermat number** is a number of the form `2^n + 1`.  The famous Fermat primes
`3 = 2^1 + 1`, `5 = 2^2 + 1`, `17 = 2^4 + 1`, `257 = 2^8 + 1`, `65537 = 2^16 + 1`
all have exponents that are powers of two (`1, 2, 4, 8, 16, …`), and this is no
accident:

    If `2^n + 1` is prime and `n ≥ 1`, then `n` is a power of two.

This is the exact analogue, for the `+1` (Fermat) family, of the classical
necessary condition on Mersenne exponents (`2^n − 1` prime ⇒ `n` prime) proved in
`MersennePrimeExponent.lean`.  Whereas a *composite* exponent kills a Mersenne
number through a **proper-divisor** factor `2^d − 1`, a Fermat number is killed by
any **odd** factor `d > 1` of the exponent, through the proper divisor `2^m + 1`
(where `n = d·m`).  Hence the surviving exponents are precisely those with no odd
factor larger than `1` — the powers of two.

The hypothesis `n ≥ 1` is genuinely needed: `2^0 + 1 = 2` is prime, yet `0` is not
a power of two.  It is the sole exception, so the full statement reads
"`n = 0` or `n` is a power of two".

## Proof

The engine is the elementary divisibility

    `d` odd  ⇒  `a + 1 ∣ a^d + 1`,

proved over `ℤ` from `a + 1 = a − (−1)` and `a^d + 1 = a^d − (−1)^d` (using
`(−1)^d = −1` for odd `d`) together with `x − y ∣ x^n − y^n`, then transferred back
to `ℕ`.

Given a Fermat prime `2^n + 1` with `n ≥ 1`, suppose `d ∣ n` is odd with `d > 1`
and write `n = d·m` (so `m ≥ 1`).  With `a = 2^m` we have
`2^n + 1 = a^d + 1`, and the divisibility above makes `a + 1 = 2^m + 1` a divisor.
Primality forces `2^m + 1 = 1` (impossible, `2^m ≥ 1`) or `2^m + 1 = 2^n + 1`,
i.e. `2^m = 2^n`, i.e. `m = n` by injectivity of `d ↦ 2^d` — contradicting
`m < n` (which holds because `d ≥ 2`, `m ≥ 1`).  So the only odd divisor of `n`
is `1`, and a positive natural whose odd part is `1` is a power of two.

Fully machine-checked and self-contained (0 sorries, 0 axioms beyond Mathlib's
foundations).
-/

namespace FermatPrimeExponent

/-- **Odd exponents preserve `a + 1` divisibility.**  For every natural `a` and
every odd `d`, `a + 1` divides `a ^ d + 1`.  (Proved over `ℤ` via
`x − y ∣ x^n − y^n` with `y = −1`, then cast back to `ℕ`.) -/
theorem add_one_dvd_pow_add_one_of_odd (a : ℕ) {d : ℕ} (hd : Odd d) :
    a + 1 ∣ a ^ d + 1 := by
  -- Work over ℤ, where `a + 1 = a - (-1)` and `a^d + 1 = a^d - (-1)^d`.
  have hz : ((a : ℤ) + 1) ∣ ((a : ℤ) ^ d + 1) := by
    have h1 : ((a : ℤ) + 1) = (a : ℤ) - (-1) := by ring
    have h2 : ((a : ℤ) ^ d + 1) = (a : ℤ) ^ d - (-1) ^ d := by
      rw [hd.neg_one_pow]; ring
    rw [h1, h2]
    exact sub_dvd_pow_sub_pow (a : ℤ) (-1) d
  -- Transfer the divisibility back to ℕ.
  have hcast : (((a + 1 : ℕ) : ℤ)) ∣ (((a ^ d + 1 : ℕ) : ℤ)) := by
    push_cast; exact hz
  exact_mod_cast hcast

/-- **Core dichotomy.**  If `2 ^ n + 1` is prime and `n ≥ 1`, then every odd
divisor of `n` equals `1`.  (An odd `d > 1` would make `2^{n/d} + 1` a proper
divisor of `2 ^ n + 1`.) -/
theorem odd_divisor_eq_one {n : ℕ} (hn : 0 < n) (hp : Nat.Prime (2 ^ n + 1)) :
    ∀ d, d ∣ n → Odd d → d = 1 := by
  intro d hdn hodd
  by_contra hd1
  -- An odd `d ≠ 1` is at least `3`, in particular `2 ≤ d`.
  have hd2 : 2 ≤ d := by
    rcases hodd with ⟨t, rfl⟩; omega
  -- Write `n = d * m`.
  obtain ⟨m, rfl⟩ := hdn
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hn
    · exact h
  -- `2 ^ (d*m) + 1 = (2^m) ^ d + 1`, so `2^m + 1` divides it (d odd).
  have hrw : (2 : ℕ) ^ (d * m) + 1 = (2 ^ m) ^ d + 1 := by
    rw [← pow_mul, Nat.mul_comm m d]
  have hdvd : (2 ^ m + 1) ∣ (2 ^ (d * m) + 1) := by
    rw [hrw]; exact add_one_dvd_pow_add_one_of_odd (2 ^ m) hodd
  -- Primality: the divisor `2^m + 1` is either `1` or the whole number.
  rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h1 | h2
  · -- `2^m + 1 = 1` is impossible since `2^m ≥ 1`.
    have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    omega
  · -- `2^m + 1 = 2^(d*m) + 1` forces `m = d*m`, contradicting `d ≥ 2`, `m ≥ 1`.
    have hpe : (2 : ℕ) ^ m = 2 ^ (d * m) := by omega
    have hmn : m = d * m := Nat.pow_right_injective (le_refl 2) hpe
    -- `m = d * m` with `m > 0` gives `d = 1`.
    have : m * 1 = m * d := by rw [mul_one, mul_comm]; exact hmn
    have hd1' : (1 : ℕ) = d := Nat.eq_of_mul_eq_mul_left hm this
    omega

/-- A positive natural whose only odd divisor is `1` is a power of two.  Proved by
strong induction: an odd `n` is its own odd divisor (so `n = 1 = 2^0`); an even
`n = 2m` inherits the hypothesis on `m` (odd divisors of `m` divide `n`), giving
`m = 2^k` and hence `n = 2^{k+1}`. -/
theorem isPowerOfTwo_of_odd_divisor_eq_one :
    ∀ {n : ℕ}, 0 < n → (∀ d, d ∣ n → Odd d → d = 1) → ∃ k, n = 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    rcases Nat.even_or_odd n with he | ho
    · -- `n` even: write `n = 2 * m` and recurse on `m`.
      obtain ⟨m, hm⟩ := he
      have hm2 : n = 2 * m := by omega
      have hmpos : 0 < m := by omega
      have hmlt : m < n := by omega
      have hmdvd : m ∣ n := ⟨2, by omega⟩
      have hh : ∀ d, d ∣ m → Odd d → d = 1 :=
        fun d hd hodd => h d (hd.trans hmdvd) hodd
      obtain ⟨k, hk⟩ := ih m hmlt hmpos hh
      exact ⟨k + 1, by rw [hm2, hk]; ring⟩
    · -- `n` odd: `n` divides itself and is odd, so `n = 1 = 2^0`.
      have : n = 1 := h n dvd_rfl ho
      exact ⟨0, by simp [this]⟩

/-- **Fermat prime exponents are powers of two.**  If `2 ^ n + 1` is prime and
`n ≥ 1`, then `n = 2 ^ k` for some `k`. -/
theorem exponent_isPowerOfTwo {n : ℕ} (hn : 0 < n) (hp : Nat.Prime (2 ^ n + 1)) :
    ∃ k, n = 2 ^ k :=
  isPowerOfTwo_of_odd_divisor_eq_one hn (odd_divisor_eq_one hn hp)

/-- Restated as the classical "`0` or a power of two" dichotomy, dropping the
positivity hypothesis (`2^0 + 1 = 2` is the sole prime with a non-power-of-two
exponent). -/
theorem exponent_zero_or_isPowerOfTwo {n : ℕ} (hp : Nat.Prime (2 ^ n + 1)) :
    n = 0 ∨ ∃ k, n = 2 ^ k := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · exact Or.inr (exponent_isPowerOfTwo h hp)

/-- Contrapositive search-pruning form: an exponent with an odd factor `> 1`
yields a composite Fermat number. -/
theorem not_prime_of_odd_factor {n d : ℕ} (hdn : d ∣ n) (hodd : Odd d)
    (hd1 : 1 < d) (hn : 0 < n) : ¬ Nat.Prime (2 ^ n + 1) :=
  fun hp => by have := odd_divisor_eq_one hn hp d hdn hodd; omega

end FermatPrimeExponent
