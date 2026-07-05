import Mathlib

/-
# Congruence Restrictions on Prime Factors of Mersenne Numbers

## Open Question (mersenne-prime-exponent-oq-02)

The base result (`mersenne-prime-exponent`) shows that if `2^n − 1` is prime then
`n` is prime.  A natural follow-up asks what can be said about the *prime factors*
of a Mersenne number `2^p − 1` when the exponent `p` is an odd prime — even when
`2^p − 1` is **not** itself prime.  The classical answer is a pair of strong
congruence restrictions:

    If `p` is an odd prime and `q` is a prime dividing `2^p − 1`, then
        q ≡ 1  (mod 2p)      and      q ≡ ±1  (mod 8).

These restrictions are exactly what makes trial division for Mersenne factors so
efficient: instead of testing every prime `q`, one only tests primes of the form
`q = 2kp + 1` that additionally lie in the residue classes `±1 (mod 8)`.  For
example, the factors of `2^11 − 1 = 23 · 89` satisfy `23 = 2·11 + 1`,
`89 = 8·11 + 1`, and `23 ≡ -1`, `89 ≡ 1 (mod 8)`.

## Proof

Fix an odd prime `p` and a prime `q ∣ 2^p − 1`.  Working in the field `ZMod q`:

* From `q ∣ 2^p − 1` we get `(2 : ZMod q)^p = 1`, so the multiplicative order of
  `2` divides the prime `p`.  Order `1` would force `2 = 1` in `ZMod q`, i.e.
  `q ∣ 1`, impossible; hence `orderOf (2 : ZMod q) = p`.

* **`q ≡ 1 (mod 2p)`.**  Fermat's little theorem gives `(2 : ZMod q)^{q-1} = 1`,
  so `p = orderOf 2 ∣ q − 1`.  Since `q` is an odd prime we also have `2 ∣ q − 1`,
  and `gcd(2, p) = 1` (as `p` is odd), so `2p ∣ q − 1`, i.e. `q ≡ 1 (mod 2p)`.

* **`q ≡ ±1 (mod 8)`.**  Because `p` is odd, write `p = 2k + 1`.  Then
  `2 = 2 · 1 = 2 · (2^p) = 2^{p+1} = (2^{k+1})^2` in `ZMod q`, so `2` is a
  quadratic residue mod `q`.  Mathlib's `ZMod.exists_sq_eq_two_iff` then gives
  `q ≡ 1` or `q ≡ 7 (mod 8)`, i.e. `q ≡ ±1 (mod 8)`.

Both statements are fully machine-checked (0 sorries, 0 axioms beyond Mathlib's
foundations).
-/

namespace MersennePrimeExponentOQ02

/-- If `q` is prime and divides the Mersenne number `2^p − 1`, then `2` has
`p`-th power equal to `1` in `ZMod q`.  This is the shared entry point for both
congruence restrictions. -/
private theorem two_pow_eq_one_of_dvd {p q : ℕ} (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : (2 : ZMod q) ^ p = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have h2p : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
  have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_sub h2p] at hz
  push_cast at hz
  rwa [sub_eq_zero] at hz

/-- `2^p − 1` is odd, hence every prime factor `q` is odd (`q ≠ 2`). -/
private theorem ne_two_of_dvd {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ p - 1) : q ≠ 2 := by
  have hmodd : Odd (2 ^ p - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow p 2 (by norm_num))
      (Nat.even_pow.mpr ⟨even_two, hp.pos.ne'⟩) odd_one
  rintro rfl
  obtain ⟨k, hk⟩ := hmodd
  obtain ⟨j, hj⟩ := hdvd
  omega

/-- **Congruence restriction mod `2p`.**  Every prime factor `q` of the Mersenne
number `2^p − 1` (for `p` an odd prime) satisfies `q ≡ 1 (mod 2p)`. -/
theorem prime_factor_congr_one_mod_two_mul {p q : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hq : q.Prime) (hdvd : q ∣ 2 ^ p - 1) : q ≡ 1 [MOD 2 * p] := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hz : (2 : ZMod q) ^ p = 1 := two_pow_eq_one_of_dvd hq hdvd
  have hq2 : q ≠ 2 := ne_two_of_dvd hp hq hdvd
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  -- `2 ≠ 0` in `ZMod q` since `q ∤ 2`.
  have ha0 : (2 : ZMod q) ≠ 0 := by
    intro h
    have hdvd2 : (q : ℕ) ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2 q).mp (by push_cast; exact h)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hdvd2)
  -- `2 ≠ 1` in `ZMod q`, so the order is not `1`.
  have hne1 : (2 : ZMod q) ≠ 1 := fun h => one_ne_zero (by linear_combination h : (1 : ZMod q) = 0)
  -- The order of `2` is exactly the prime `p`.
  have hord : orderOf (2 : ZMod q) = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hz) with h1 | hpp
    · exact absurd (orderOf_eq_one_iff.mp h1) hne1
    · exact hpp
  -- Fermat: order divides `q − 1`, hence `p ∣ q − 1`.
  have hp_dvd : p ∣ q - 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha0)
  -- `q` odd gives `2 ∣ q − 1`.
  have h2_dvd : 2 ∣ q - 1 := by
    obtain ⟨k, hk⟩ := hqodd; exact ⟨k, by omega⟩
  -- Combine coprime divisors: `2p ∣ q − 1`.
  have hpne2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hpodd
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hpne2)
  have h2p_dvd : 2 * p ∣ q - 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd hp_dvd
  exact ((Nat.modEq_iff_dvd' hq.pos).mpr h2p_dvd).symm

/-- **Congruence restriction mod `8`.**  Every prime factor `q` of the Mersenne
number `2^p − 1` (for `p` an odd prime) satisfies `q ≡ ±1 (mod 8)`, expressed as
`q % 8 = 1 ∨ q % 8 = 7`. -/
theorem prime_factor_pm_one_mod_eight {p q : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hq : q.Prime) (hdvd : q ∣ 2 ^ p - 1) : q % 8 = 1 ∨ q % 8 = 7 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hz : (2 : ZMod q) ^ p = 1 := two_pow_eq_one_of_dvd hq hdvd
  have hq2 : q ≠ 2 := ne_two_of_dvd hp hq hdvd
  -- `2` is a quadratic residue mod `q`: with `p = 2k+1`, `2 = (2^{k+1})²`.
  have hsq : IsSquare (2 : ZMod q) := by
    obtain ⟨k, hk⟩ := hpodd
    refine ⟨(2 : ZMod q) ^ (k + 1), ?_⟩
    have h1 : (2 : ZMod q) ^ (k + 1) * (2 : ZMod q) ^ (k + 1)
        = (2 : ZMod q) ^ p * (2 : ZMod q) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [h1, hz, one_mul]
  exact (ZMod.exists_sq_eq_two_iff hq2).mp hsq

end MersennePrimeExponentOQ02
