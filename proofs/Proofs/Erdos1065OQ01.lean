import Mathlib

/-!
# Erdős #1065, child OQ-01: uniqueness of the `2^k · q` representation

Erdős Problem #1065 asks whether there are infinitely many primes of the form
`2^k · q + 1` with `q` an odd prime and `k ≥ 1`. The parent files
(`erdos-1065`, `erdos-1065-incomplete-01`) build the `twoVal`/`oddPart`
machinery and characterise such "form-A" primes.

Underpinning every such argument is a basic uniqueness fact that this entry
isolates and fully verifies:

> **Unique `2^k · q` form.** If `2^{a} · m = 2^{b} · n` with `m, n` odd, then
> `a = b` and `m = n`.

The `2`-adic valuation reads off the exponent: `v₂(2^a · m) = a` when `m` is odd
(`factorization_two_pow_mul_odd`), so the two exponents agree and cancellation
gives the odd parts. As a corollary, the form-A representation of a prime is
unique (`formA_repr_unique`): the pair `(k, q)` in `p = 2^k · q + 1` (with `q`
odd) is determined by `p`.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## References
* Erdős Problem #1065 (primes of the form `2^k · q + 1`).
* 2-adic valuation and `Nat.factorization`.
-/

namespace Erdos1065OQ01

open Nat

/-!
## Section 1: the 2-adic valuation reads off the exponent
-/

/-- **`v₂(2^a · m) = a` for odd `m`.** The `2`-adic valuation of `2^a · m` is
    exactly `a` when `m` is odd, since `m` contributes no factor of `2`. -/
theorem factorization_two_pow_mul_odd {a m : ℕ} (hm : Odd m) :
    (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by rintro rfl; rw [Nat.odd_iff] at hm; omega
  have h2m : ¬ (2 ∣ m) := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hm)
  rw [Nat.factorization_mul (pow_ne_zero a two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2m, add_zero, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]

/-!
## Section 2: uniqueness of the `2^k · q` representation
-/

/-- **Uniqueness of the `2^a · m` form.** If `2^a · m = 2^b · n` with `m` and `n`
    odd, then `a = b` and `m = n`: the exponents agree by comparing `2`-adic
    valuations, and the odd parts agree by cancelling `2^a`. -/
theorem two_pow_mul_odd_unique {a b m n : ℕ} (hm : Odd m) (hn : Odd n)
    (h : 2 ^ a * m = 2 ^ b * n) : a = b ∧ m = n := by
  have ha : a = b := by
    have hval := congrArg (fun x => x.factorization 2) h
    simpa [factorization_two_pow_mul_odd hm, factorization_two_pow_mul_odd hn] using hval
  subst ha
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) a) h⟩

/-- **The form-A representation of a prime is unique.** If `p = 2^{k₁} · q₁ + 1
    = 2^{k₂} · q₂ + 1` with `q₁, q₂` odd, then `k₁ = k₂` and `q₁ = q₂`. So the
    pair `(k, q)` in Erdős #1065's form `2^k · q + 1` is determined by `p`. -/
theorem formA_repr_unique {k₁ k₂ q₁ q₂ : ℕ} (hq₁ : Odd q₁) (hq₂ : Odd q₂)
    (h : 2 ^ k₁ * q₁ + 1 = 2 ^ k₂ * q₂ + 1) : k₁ = k₂ ∧ q₁ = q₂ :=
  two_pow_mul_odd_unique hq₁ hq₂ (by omega)

/-- The exponent `k` of a form-A number `p = 2^k · q + 1` (odd `q`) is recovered
    as the `2`-adic valuation of `p − 1`. -/
theorem formA_exponent_eq {k q : ℕ} (hq : Odd q) :
    ((2 ^ k * q + 1) - 1).factorization 2 = k := by
  simpa using factorization_two_pow_mul_odd (a := k) hq

/-!
## Section 3: a concrete instance
-/

/-- `41 = 2³ · 5 + 1` with `5` an odd prime, so `41` is a form-A prime, and by
    `formA_repr_unique` this representation `(k, q) = (3, 5)` is the only one. -/
theorem formA_41 : (41 : ℕ) = 2 ^ 3 * 5 + 1 ∧ Odd (5 : ℕ) ∧ Nat.Prime 5 := by
  refine ⟨by norm_num, by decide, by norm_num⟩

end Erdos1065OQ01
