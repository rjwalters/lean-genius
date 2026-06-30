/-
  A Fermat-Number Lemma: 2^m + 1 Prime Forces m to Be a Power of Two

  Open Question (angle-trisection-oq-01-oq-04-oq-02):
  "If 2^m + 1 is prime then m is a power of two. If m had an odd factor d > 1,
   m = d·k, then 2^k + 1 divides 2^m + 1 = (2^k)^d + 1, contradicting primality.
   Supports Gauss–Wantzel: a regular p-gon is constructible iff p is a Fermat prime."

  This is the exponent half of the theory of Fermat primes. Mathlib proves the bare
  *existence* statement `Nat.pow_of_pow_add_prime` (a^n + 1 prime ⟹ ∃ m, n = 2^m), but
  not the *constructive* obstruction that drives it. We supply that obstruction with an
  EXPLICIT witness:

    if d is an odd factor of m with d > 1, then 2^(m/d) + 1 is a genuine *proper*
    divisor of 2^m + 1 — strictly between 1 and 2^m + 1 — so 2^m + 1 is composite.

  From this constructive compositeness criterion we derive, independently of Mathlib's
  `pow_of_pow_add_prime`, the Fermat-prime exponent law: `2^m + 1` prime ⟹ `m = 2^k`.
  The explicit factor is what a primality search actually exhibits (e.g. 2^6 + 1 = 65 has
  the odd exponent-factor 3, yielding the divisor 2^2 + 1 = 5), and is the form needed in
  the Gauss–Wantzel program for constructible regular polygons.

  Tags: number-theory, fermat-primes, gauss-wantzel, divisibility, constructive
-/

import Mathlib

namespace AngleTrisectionOQ01OQ04OQ02

open Nat

/-! ## Part I. The divisibility engine.

For odd `d`, `x + y ∣ x^d + y^d`. Specialising `x = 2^k`, `y = 1` gives the exact
factor that obstructs primality of `2^(k·d) + 1`. -/

/-- For any odd exponent-multiplier `d`, `2^k + 1` divides `2^(k·d) + 1`.
This is the algebraic core: `2^(k·d) + 1 = (2^k)^d + 1^d` and `a + b ∣ a^d + b^d`
whenever `d` is odd. -/
theorem two_pow_add_one_dvd (k d : ℕ) (hd : Odd d) :
    2 ^ k + 1 ∣ 2 ^ (k * d) + 1 := by
  have h := hd.nat_add_dvd_pow_add_pow (2 ^ k) 1
  rwa [one_pow, ← pow_mul] at h

/-! ## Part II. The constructive obstruction (beyond Mathlib).

An odd factor `d > 1` of the exponent `m` produces an explicit proper divisor of
`2^m + 1`, hence compositeness. Mathlib states only the existence half; this records
the divisor explicitly. -/

/-- **Constructive compositeness.** If `m` has an odd factor `d > 1`, then `2^m + 1`
is not prime — witnessed by the explicit proper divisor `2^(m/d) + 1`. -/
theorem not_prime_two_pow_add_one_of_odd_factor {m d : ℕ}
    (hd : Odd d) (hd1 : 1 < d) (hdvd : d ∣ m) (hm : m ≠ 0) :
    ¬ (2 ^ m + 1).Prime := by
  obtain ⟨k, rfl⟩ := hdvd
  -- `m = d * k`; from `m ≠ 0` both factors are positive.
  rw [Nat.mul_ne_zero_iff] at hm
  obtain ⟨hd0, hk0⟩ := hm
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  -- the explicit divisor `2^k + 1` of `2^(d*k) + 1`
  have hdvd2 : 2 ^ k + 1 ∣ 2 ^ (d * k) + 1 := by
    rw [Nat.mul_comm d k]; exact two_pow_add_one_dvd k d hd
  intro hp
  rcases (hp.eq_one_or_self_of_dvd _ hdvd2) with h1 | hself
  · -- `2^k + 1 = 1` is impossible
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  · -- `2^k + 1 = 2^(d*k) + 1` forces `k = d*k`, impossible for `d > 1`, `k ≥ 1`
    have hkeq : 2 ^ k = 2 ^ (d * k) := by omega
    have : k = d * k := Nat.pow_right_injective (le_refl 2) hkeq
    -- but `d * k ≥ 2 * k > k` since `d ≥ 2`, `k ≥ 1`
    nlinarith [hd1, hk1]

/-! ## Part III. The Fermat-prime exponent law.

Independently of Mathlib's `pow_of_pow_add_prime`, the constructive obstruction yields:
a prime of the form `2^m + 1` must have `m` a power of two. -/

/-- **Fermat-prime exponent law.** If `2^m + 1` is prime (`m ≠ 0`), then `m` is a power
of two. Proof: factor `m = 2^k · d` with `d` odd; if `d > 1`, Part II makes `2^m + 1`
composite, so `d = 1` and `m = 2^k`. -/
theorem isPowerOfTwo_of_prime {m : ℕ} (hm : m ≠ 0) (hP : (2 ^ m + 1).Prime) :
    ∃ k : ℕ, m = 2 ^ k := by
  obtain ⟨k, d, hd, hmeq⟩ := Nat.exists_eq_two_pow_mul_odd hm
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · -- `d` odd and `d < 2` ⟹ `d = 1` ⟹ `m = 2^k`
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd
    have : d = 1 := by omega
    exact ⟨k, by rw [hmeq, this, Nat.mul_one]⟩
  · -- `d ≥ 2`, and `d` odd ⟹ `d > 1` ⟹ contradiction with primality
    exfalso
    have hdvd : d ∣ m := ⟨2 ^ k, by rw [hmeq]; ring⟩
    exact not_prime_two_pow_add_one_of_odd_factor hd (by omega) hdvd hm hP

/-! ## Part IV. Concrete witnesses. -/

/-- `2^6 + 1 = 65 = 5 · 13` is composite: the exponent `6 = 2 · 3` has the odd factor `3`,
yielding the explicit proper divisor `2^(6/3) + 1 = 2^2 + 1 = 5`. -/
theorem not_prime_two_pow_six_add_one : ¬ (2 ^ 6 + 1).Prime :=
  not_prime_two_pow_add_one_of_odd_factor (d := 3) (by decide) (by decide) (by decide) (by decide)

/-- Contrapositive convenience form: a prime exponent of a Fermat prime is a power of two,
so the only candidate exponents are `1, 2, 4, 8, 16, …`. -/
theorem exponent_isPowerOfTwo {m : ℕ} (hm : m ≠ 0) (hP : (2 ^ m + 1).Prime) :
    ∃ k, m = 2 ^ k := isPowerOfTwo_of_prime hm hP

end AngleTrisectionOQ01OQ04OQ02
