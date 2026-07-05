import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Mersenne Prime Exponents Are Prime

## Open Question (mersenne-prime-exponent)

A **Mersenne number** is a number of the form `2^n - 1`.  A **Mersenne prime**
is a Mersenne number that happens to be prime (`3 = 2² − 1`, `7 = 2³ − 1`,
`31 = 2⁵ − 1`, `127 = 2⁷ − 1`, …).  The exponents `2, 3, 5, 7, …` are all prime,
and this is no accident:

    If `2^n − 1` is prime, then `n` is prime.

This is the classical necessary condition on Mersenne exponents — the
prerequisite that lets the Lucas–Lehmer test restrict its search to prime `n`.
The converse is false (`2¹¹ − 1 = 2047 = 23 · 89`), so primality of the exponent
is necessary but not sufficient.

## Proof

Contrapositive on the exponent.  Suppose `2^n − 1` is prime but `n` is **not**.

* First, `n ≥ 2`: the degenerate exponents give `2⁰ − 1 = 0` and `2¹ − 1 = 1`,
  neither of which is prime, so a prime Mersenne number forces `n ≥ 2`.

* A composite `n ≥ 2` has a nontrivial divisor `d` with `2 ≤ d < n`
  (`Nat.exists_dvd_of_not_prime2`).

* Divisibility of exponents lifts to divisibility of Mersenne numbers:
  `d ∣ n ⇒ 2^d − 1 ∣ 2^n − 1` (`Nat.pow_sub_one_dvd_pow_sub_one`, itself a
  corollary of `x − y ∣ xⁿ − yⁿ`).

* But `2^d − 1` is a *proper* divisor of `2^n − 1`: from `2 ≤ d` we get
  `2^d − 1 ≥ 3 > 1`, and from `d < n` we get `2^d < 2^n`, hence
  `2^d − 1 < 2^n − 1`.  A prime has no proper divisor strictly between `1` and
  itself, contradicting the primality of `2^n − 1`.

Both escape hatches offered by primality are closed using injectivity of
`d ↦ 2^d` (`Nat.pow_right_injective`): `2^d − 1 = 1` would force `d = 1`, and
`2^d − 1 = 2^n − 1` would force `d = n`.

The result is fully machine-checked and self-contained (0 sorries, 0 axioms
beyond Mathlib's foundations).
-/

namespace MersennePrimeExponent

/-- **Mersenne prime exponents are prime.**  If the Mersenne number `2^n − 1`
is prime, then the exponent `n` is prime. -/
theorem prime_of_mersenne_prime {n : ℕ} (hp : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by
  by_contra hn
  -- A prime Mersenne number forces the exponent to be at least 2.
  have hn2 : 2 ≤ n := by
    match n with
    | 0 => norm_num at hp          -- `2⁰ − 1 = 0` is not prime
    | 1 => norm_num at hp          -- `2¹ − 1 = 1` is not prime
    | (k + 2) => omega
  -- A composite `n ≥ 2` has a nontrivial divisor `2 ≤ d < n`.
  obtain ⟨d, hd_dvd, hd2, hdn⟩ := Nat.exists_dvd_of_not_prime2 hn2 hn
  -- Exponent divisibility lifts to Mersenne-number divisibility.
  have hdvd : 2 ^ d - 1 ∣ 2 ^ n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hd_dvd
  -- Primality of `2^n − 1` says its only divisors are `1` and itself.
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h2
  · -- `2^d − 1 = 1` is impossible: `d ≥ 2 ⇒ 2^d ≥ 4`.
    have h4 : 4 ≤ 2 ^ d := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd2
    omega
  · -- `2^d − 1 = 2^n − 1` forces `2^d = 2^n`, hence `d = n`, contradicting `d < n`.
    have h2d : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by norm_num)
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    have heq : 2 ^ d = 2 ^ n := by omega
    have : d = n := Nat.pow_right_injective (le_refl 2) heq
    omega

/-- Restated with the explicit `2^n − 1` phrasing used in the gallery. -/
theorem mersenne_exponent_prime (n : ℕ) (hp : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n :=
  prime_of_mersenne_prime hp

/-- The contrapositive form: a composite exponent yields a composite Mersenne
number.  Useful as the direct search-pruning statement for Lucas–Lehmer. -/
theorem not_prime_mersenne_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime n) :
    ¬ Nat.Prime (2 ^ n - 1) :=
  fun hp => hn (prime_of_mersenne_prime hp)

end MersennePrimeExponent
