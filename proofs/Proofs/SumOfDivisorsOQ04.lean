/-
# Sum of Divisors OQ-04: structural identities for σₖ — primes, prime powers, multiplicativity

## Open Question
The base entry verifies σ(p) = p + 1 for *specific* primes and classifies particular
perfect / abundant / amicable numbers. This entry proves the *general* structural laws of
the divisor-sum function: σ on an arbitrary prime, the closed geometric form on prime
powers, the multiplicative evaluation on a product of two distinct primes, and the σ-form
of perfection.

## Approach
Everything is read off Mathlib's `ArithmeticFunction.sigma` and its prime-power /
multiplicative API:
  * `sigma_one_apply_prime_pow` / `sigma_zero_apply_prime_pow` give σ and τ on `p ^ i`.
  * `geom_sum_mul` turns the open sum `∑ pᵏ` into the closed form `(pⁱ⁺¹ − 1)/(p − 1)`.
  * `IsMultiplicative.map_mul_of_coprime` (with `coprime_primes`) evaluates σ on `p · q`.
  * `Nat.perfect_iff_sum_divisors_eq_two_mul` + `sigma_one_apply` express perfection as
    `σ(n) = 2n`.

These are the foundational identities behind the base entry's numerical classifications,
proved once and for all in `n`, `p`, `q`, `i` rather than for hand-picked values.

Sorry-free and axiom-free.
-/
import Mathlib

namespace SumOfDivisorsOQ04

open ArithmeticFunction Finset

/-- **`σ(p) = p + 1` for every prime `p`.** The general theorem behind the base entry's
case-by-case checks: a prime's only divisors are `1` and `p`. -/
theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  have h := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  rw [pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  ring

/-- **`τ(p) = σ₀(p) = 2` for every prime `p`.** A prime has exactly two divisors. -/
theorem sigma_zero_prime {p : ℕ} (hp : p.Prime) : sigma 0 p = 2 := by
  have h := sigma_zero_apply_prime_pow (p := p) (i := 1) hp
  rw [pow_one] at h
  simpa using h

/-- **Closed geometric form on prime powers:** `σ(pⁱ) · (p − 1) = pⁱ⁺¹ − 1` (over ℤ).
`sigma_one_apply_prime_pow` writes `σ(pⁱ)` as the open sum `∑_{k<i+1} pᵏ`; `geom_sum_mul`
collapses it. Equivalently `σ(pⁱ) = (pⁱ⁺¹ − 1)/(p − 1)`. -/
theorem sigma_one_prime_pow_mul {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (sigma 1 (p ^ i) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (i + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_mul]

/-- **Multiplicativity on two distinct primes:** `σ(p · q) = (p + 1)(q + 1)`. Distinct
primes are coprime (`coprime_primes`), so `σ` factors (`isMultiplicative_sigma`), and each
factor is `sigma_one_prime`. -/
theorem sigma_one_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sigma 1 (p * q) = (p + 1) * (q + 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp, sigma_one_prime hq]

/-- **Perfection in σ-form:** for `n > 0`, `n` is perfect iff `σ(n) = 2n`. Ties the
divisor-sum function to the base entry's perfect numbers (`σ(6) = 12 = 2·6`,
`σ(28) = 56 = 2·28`). -/
theorem perfect_iff_sigma_one {n : ℕ} (hn : 0 < n) :
    Nat.Perfect n ↔ sigma 1 n = 2 * n := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hn, sigma_one_apply]

end SumOfDivisorsOQ04
