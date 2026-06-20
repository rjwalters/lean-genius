/-
# Sum of Divisors OQ-07: the closed geometric-product form of σₖ for *every* exponent k

## Open Question
Mathlib evaluates the divisor-power sum `σₖ` only in **open** form: on a prime power it
gives the geometric *sum* `σₖ(pⁱ) = ∑_{j≤i} p^{jk}` (`sigma_apply_prime_pow`), and over a
factorisation it gives the *product of sums*
`σₖ(n) = ∏_{p∣n} ∑_{j≤vₚ(n)} p^{jk}`
(`sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul`). The gallery's OQ-04 collapses
the inner geometric series into closed form, but **only for `k = 1`**
(`sigma_one_prime_pow_mul : σ(pⁱ)·(p−1) = p^{i+1}−1`). This entry proves the closed
geometric-product form for an **arbitrary** power `k`.

## Results
* `geom_sigma_sum` — the underlying geometric identity over ℤ:
  `(∑_{j≤i} p^{jk})·(pᵏ−1) = p^{k(i+1)}−1`.
* `sigma_prime_pow_mul` — closed form on a prime power, all `k`:
  `σₖ(pⁱ)·(pᵏ−1) = p^{k(i+1)}−1`  (the `k = 1` case is OQ-04's `sigma_one_prime_pow_mul`).
* `sigma_two_primes_pow_mul` — closed form on `pᵃ·qᵇ` via multiplicativity:
  `σₖ(pᵃqᵇ)·(pᵏ−1)(qᵏ−1) = (p^{k(a+1)}−1)(q^{k(b+1)}−1)`.
* `sigma_mul_prod_primeFactors` — the general closed geometric-product form:
  `σₖ(n)·∏_{p∣n}(pᵏ−1) = ∏_{p∣n}(p^{k(vₚ(n)+1)}−1)`,
  collapsing Mathlib's product-of-sums into a product of closed quotients.

## Approach
Everything reduces to `geom_sum_mul` applied to the base `x = pᵏ`. The prime-power case
rewrites `σₖ(pⁱ)` via `sigma_apply_prime_pow` and collapses the geometric sum; the full
factorisation case starts from Mathlib's product-of-sums, distributes the product of
`(pᵏ−1)` factors with `Finset.prod_mul_distrib`, and collapses each factor with
`geom_sigma_sum`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace SumOfDivisorsOQ07

open ArithmeticFunction Finset

/-- **Geometric collapse over ℤ.** For any base `p` and exponent `k`,
`(∑_{j<i+1} p^{jk})·(pᵏ−1) = p^{k(i+1)}−1`. This is `geom_sum_mul` with base `x = pᵏ`,
re-indexed so the summand reads `p^{jk}` (the shape produced by `sigma_apply_prime_pow`). -/
theorem geom_sigma_sum (k p i : ℕ) :
    (∑ j ∈ range (i + 1), (p : ℤ) ^ (j * k)) * ((p : ℤ) ^ k - 1)
      = (p : ℤ) ^ (k * (i + 1)) - 1 := by
  have hsum : (∑ j ∈ range (i + 1), (p : ℤ) ^ (j * k))
      = ∑ j ∈ range (i + 1), ((p : ℤ) ^ k) ^ j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm]
  rw [hsum, geom_sum_mul, ← pow_mul]

/-- **Closed geometric form on a prime power, for every `k`:**
`σₖ(pⁱ)·(pᵏ−1) = p^{k(i+1)}−1` (over ℤ). Generalises OQ-04's `sigma_one_prime_pow_mul`
(the `k = 1` case) to arbitrary exponents. Equivalently `σₖ(pⁱ) = (p^{k(i+1)}−1)/(pᵏ−1)`. -/
theorem sigma_prime_pow_mul {k p i : ℕ} (hp : p.Prime) :
    (sigma k (p ^ i) : ℤ) * ((p : ℤ) ^ k - 1) = (p : ℤ) ^ (k * (i + 1)) - 1 := by
  rw [sigma_apply_prime_pow hp]
  push_cast
  exact geom_sigma_sum k p i

/-- **Closed form on a two-prime product `pᵃ·qᵇ`.** Distinct primes give coprime prime
powers, so `σₖ` factors (`isMultiplicative_sigma`) and each factor collapses by
`sigma_prime_pow_mul`:
`σₖ(pᵃqᵇ)·(pᵏ−1)(qᵏ−1) = (p^{k(a+1)}−1)(q^{k(b+1)}−1)`. -/
theorem sigma_two_primes_pow_mul {k p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    (sigma k (p ^ a * q ^ b) : ℤ) * (((p : ℤ) ^ k - 1) * ((q : ℤ) ^ k - 1))
      = ((p : ℤ) ^ (k * (a + 1)) - 1) * ((q : ℤ) ^ (k * (b + 1)) - 1) := by
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes hp hq).mpr hpq)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  have h1 := sigma_prime_pow_mul (k := k) (p := p) (i := a) hp
  have h2 := sigma_prime_pow_mul (k := k) (p := q) (i := b) hq
  push_cast
  linear_combination
    ((sigma k (q ^ b) : ℤ) * ((q : ℤ) ^ k - 1)) * h1
      + ((p : ℤ) ^ (k * (a + 1)) - 1) * h2

/-- **General closed geometric-product form.** For `n ≠ 0`,
`σₖ(n)·∏_{p∣n}(pᵏ−1) = ∏_{p∣n}(p^{k(vₚ(n)+1)}−1)`.
This collapses Mathlib's product-of-sums
`sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` into a product of closed
geometric quotients, generalising the prime-power identity across the whole factorisation. -/
theorem sigma_mul_prod_primeFactors {k n : ℕ} (hn : n ≠ 0) :
    (sigma k n : ℤ) * ∏ p ∈ n.primeFactors, ((p : ℤ) ^ k - 1)
      = ∏ p ∈ n.primeFactors, ((p : ℤ) ^ (k * (n.factorization p + 1)) - 1) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  exact geom_sigma_sum k p (n.factorization p)

end SumOfDivisorsOQ07
