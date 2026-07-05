/-
# Sum of Divisors OQ-06-01: the product formula for the divisor-counting function τ

## Open Question
The parent entry (OQ-06) proves the *parity* criterion `τ(n) odd ⟺ n is a perfect square`,
using the prime-factorisation form of `τ = σ₀` internally. This follow-up isolates and
packages the underlying **multiplicative structure of τ itself** as a standalone gallery
identity, exactly as requested by the pool note:

  **τ(n) = ∏_{p ∣ n} (vₚ(n) + 1)**,  and in particular  **τ(pᵃ) = a + 1**.

## Honest scope note
Mathlib already contains the two headline facts in `Finsupp.prod` form
(`Nat.card_divisors`) and for coprime products (`Nat.Coprime.card_divisors_mul`). The value
this entry adds over a raw citation is:

  1. A gallery-facing restatement of the formula as an ordinary product `∏ p ∈ n.primeFactors`.
  2. The prime-power specialisation `τ(pᵃ) = a + 1` (derived from `Nat.divisors_prime_pow`),
     which Mathlib does not state directly, together with its `τ(p) = 2` corollary.
  3. A **sharpness** result: the coprimality hypothesis in the multiplicative law is
     genuinely necessary — `τ(2·2) = 3 ≠ 4 = τ(2)·τ(2)`. This is the theory-level content
     that distinguishes "multiplicative on coprimes" from "completely multiplicative", and
     it is not recorded anywhere in the gallery.

Sorry-free and axiom-free.
-/
import Mathlib

namespace SumOfDivisorsOQ06OQ01

open ArithmeticFunction Finset

/-- **The divisor-counting product formula.** For `n ≠ 0`,
`τ(n) = ∏_{p ∈ primeFactors n} (vₚ(n) + 1)`. This is `Nat.card_divisors` rephrased from the
`Finsupp.prod` over the factorisation support to an ordinary `Finset.prod` over the prime
factors, the form used in elementary number theory. -/
theorem card_divisors_eq_prod {n : ℕ} (hn : n ≠ 0) :
    #n.divisors = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
  rw [Nat.card_divisors hn, ← Nat.support_factorization]

/-- **Divisor count of a prime power.** `τ(pᵃ) = a + 1`. The divisors of `pᵃ` are exactly
`p⁰, p¹, …, pᵃ`, giving `a + 1` of them. -/
theorem card_divisors_prime_pow {p : ℕ} (pp : p.Prime) (a : ℕ) :
    #(p ^ a).divisors = a + 1 := by
  rw [Nat.divisors_prime_pow pp, Finset.card_map, Finset.card_range]

/-- **A prime has exactly two divisors.** The `a = 1` case of the prime-power formula. -/
theorem card_divisors_prime {p : ℕ} (pp : p.Prime) : #p.divisors = 2 := by
  have h := card_divisors_prime_pow pp 1
  rwa [pow_one] at h

/-- **Multiplicativity on coprime arguments.** For coprime `m, n`,
`τ(m·n) = τ(m)·τ(n)`. Re-exported from `Nat.Coprime.card_divisors_mul` so the product
formula and its multiplicative law live together in one entry. -/
theorem card_divisors_coprime_mul {m n : ℕ} (h : m.Coprime n) :
    #(m * n).divisors = #m.divisors * #n.divisors :=
  Nat.Coprime.card_divisors_mul h

/-- **Sharpness of the coprimality hypothesis.** The multiplicative law fails without
coprimality: with `m = n = 2` (so `gcd = 2 ≠ 1`),
`τ(4) = 3` while `τ(2)·τ(2) = 4`. Hence `τ` is multiplicative but **not** completely
multiplicative — the coprimality hypothesis in `card_divisors_coprime_mul` cannot be
dropped. -/
theorem card_divisors_mul_ne_of_not_coprime :
    #(2 * 2 : ℕ).divisors ≠ #(2 : ℕ).divisors * #(2 : ℕ).divisors := by decide

/-- The failing pair really is non-coprime, pinning down why the law does not apply. -/
theorem not_coprime_two_two : ¬ (2 : ℕ).Coprime 2 := by decide

/-! ### Worked computations via the product formula -/

/-- `12 = 2²·3`, so `τ(12) = (2+1)(1+1) = 6`. -/
example : #(12 : ℕ).divisors = 6 := by decide

/-- `100 = 2²·5²`, so `τ(100) = (2+1)(2+1) = 9`. -/
example : #(100 : ℕ).divisors = 9 := by decide

/-- Assembling `τ(12)` from its coprime prime-power factors `4` and `3` via the
multiplicative law: `τ(4·3) = τ(4)·τ(3) = 3·2 = 6` (and `4·3 = 12`). -/
example : #(4 * 3 : ℕ).divisors = #(4 : ℕ).divisors * #(3 : ℕ).divisors :=
  card_divisors_coprime_mul (by decide)

/-- The same via the prime-power formula: `τ(2⁵) = 6`. -/
example : #(2 ^ 5 : ℕ).divisors = 6 := card_divisors_prime_pow (by norm_num) 5

end SumOfDivisorsOQ06OQ01
