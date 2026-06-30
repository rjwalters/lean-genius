/-
# Euler's Odd-Perfect Form — the special-prime existence step

This file continues the global assembly of Euler's structural theorem for odd
perfect numbers, building on:

* `SumOfDivisorsOQ01.lean` — the local prime-power engine (L1 parity law, L2
  mod-4 characterization, the `(1+p)·S` pairing identity).
* `SumOfDivisorsOQ01SquarePacking.lean` — the square-packaging half:
  `odd_sigma_odd_iff_isSquare` (for odd `N`, `σ(N)` is odd ⟺ `N` is a square)
  and `odd_perfect_not_isSquare` (an odd perfect number is never a square).

## Euler's form and the three remaining steps

Euler (1747): an odd perfect `N` has the form `N = p^a·m²` with `p` the special
prime, `p ≡ a ≡ 1 (mod 4)`, `gcd(p, m) = 1`.  The global assembly splits into:

1. **Existence of a special prime (this file).**  Since `σ(N) = 2N` is even, the
   square-packaging law forces `N` to be a non-square, hence *some* prime divides
   `N` to an odd power.  `odd_perfect_exists_special_prime` records this gateway
   fact: the candidate special prime exists.

2. **Uniqueness / counting (deferred).**  Writing `v₂(σ N)` as a *sum* over the
   prime factors (multiplicativity of `σ` + additivity of `Nat.factorization`
   over products, `Nat.factorization_prod`), each odd-exponent prime contributes
   `≥ 1` to the 2-adic valuation while even-exponent primes contribute `0`
   (L1).  Because `v₂(σ N) = v₂(2N) = 1` for odd `N`, there is **exactly one**
   odd-exponent prime `p₀`, and its contribution is exactly `1`.

3. **Mod-4 pin (deferred).**  That unit contribution `v₂(σ(p₀^{a₀})) = 1` is
   exactly the hypothesis of L2 (`sigma_prime_pow_mod_four`), which pins
   `p₀ ≡ a₀ ≡ 1 (mod 4)`.  The remaining factor `N / p₀^{a₀}` has all-even
   exponents, hence is a square `m²` by `isSquare_iff_even_factorization`.

## Roadmap for step 2 (confirmed Mathlib lemmas, mathlib v4.26.0)

* `ArithmeticFunction.multiplicative_factorization` + `isMultiplicative_sigma`
  — `σ N = ∏_{p ∈ N.primeFactors} σ(p^{e_p})` (already used in the packing file).
* `Nat.factorization_prod` — `(∏ x ∈ S, g x).factorization = ∑ x ∈ S, (g x).factorization`
  (needs each `g x ≠ 0`; `σ` of a positive is positive).
* Evaluate the resulting Finsupp sum at the prime `2` (`Finset.sum_apply'` /
  `Finsupp.finset_sum_apply`) to get `v₂(σ N) = ∑_p v₂(σ(p^{e_p}))`.
* `sigma_prime_pow_odd_iff` (L1) — even-exponent terms vanish; the `= 1` total
  with each odd-exponent term `≥ 1` forces a unique special prime.

All results are conditional structure theorems and assume nothing about the
existence of odd perfect numbers (open).
-/
import Mathlib
import Proofs.SumOfDivisorsOQ01
import Proofs.SumOfDivisorsOQ01SquarePacking

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace SumOfDivisorsOQ01

/-- **Existence of the special prime (gateway to Euler's form).**

An odd perfect number `N` has at least one prime factor occurring to an *odd*
power.  This is the existence half of Euler's "special prime": because
`σ(N) = 2N` is even, the square-packaging parity law (`odd_perfect_not_isSquare`)
makes `N` a non-square, so not every exponent in its factorization is even.

The follow-up (deferred) counting step upgrades "at least one" to "exactly one"
and then L2 (`sigma_prime_pow_mod_four`) pins that prime and exponent to
`1 (mod 4)`. -/
theorem odd_perfect_exists_special_prime
    {N : ℕ} (hodd : Odd N) (hperf : Nat.Perfect N) :
    ∃ p ∈ N.primeFactors, Odd (N.factorization p) := by
  have hN : N ≠ 0 := hperf.2.ne'
  have hns : ¬ IsSquare N := odd_perfect_not_isSquare hodd hperf
  rw [isSquare_iff_even_factorization hN, not_forall] at hns
  obtain ⟨p, hp⟩ := hns
  rw [not_even_iff_odd] at hp
  have hfne : N.factorization p ≠ 0 := by
    have := Nat.odd_iff.mp hp; omega
  refine ⟨p, ?_, hp⟩
  rw [← Nat.support_factorization]
  exact Finsupp.mem_support_iff.mpr hfne

end SumOfDivisorsOQ01
