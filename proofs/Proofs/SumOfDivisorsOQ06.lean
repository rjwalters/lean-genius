/-
# Sum of Divisors OQ-06: the number of divisors τ(n) is odd ⟺ n is a perfect square

## Open Question
The base entry and OQ-04 develop the divisor-*sum* `σ₁` and read off `σ₀ = τ`, the number
of divisors, only on primes and prime powers. This entry proves the classical parity
criterion for the divisor-counting function itself:

  **τ(n) is odd ⟺ n is a perfect square.**

Equivalently, `#n.divisors` is odd exactly when `n = r²` for some `r`. This is the cleanest
non-trivial structural fact about `σ₀` and it is absent from both Mathlib and the gallery
(Mathlib has `Nat.card_divisors` but no parity / square characterisation of it).

## Approach
Everything reduces to the prime factorisation:
  * `Nat.card_divisors` writes `τ(n) = ∏_{p ∣ n} (vₚ(n) + 1)`.
  * A product of naturals is odd ⟺ every factor is odd (`odd_prod_iff`, proved by
    induction with `Nat.odd_mul`).
  * `vₚ(n) + 1` is odd ⟺ `vₚ(n)` is even, so τ(n) is odd ⟺ every exponent is even.
  * `n` is a perfect square ⟺ every exponent `vₚ(n)` is even
    (`isSquare_iff_factorization_even`), the forward direction from
    `Nat.factorization_mul`, the reverse by reassembling `r = ∏ p^{vₚ(n)/2}` and using
    `Nat.factorization_prod_pow_eq_self`.

Sorry-free and axiom-free.
-/
import Mathlib

namespace SumOfDivisorsOQ06

open ArithmeticFunction Finset

/-- **A product of naturals is odd iff every factor is odd.** Elementary induction on the
index set using `Nat.odd_mul`. -/
theorem odd_prod_iff (s : Finset ℕ) (f : ℕ → ℕ) :
    Odd (∏ i ∈ s, f i) ↔ ∀ i ∈ s, Odd (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Nat.odd_mul, ih]
      constructor
      · rintro ⟨hfa, hrest⟩ i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hfa
        · exact hrest i hi
      · intro h
        exact ⟨h a (Finset.mem_insert_self a s),
               fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- **A positive natural is a perfect square iff every prime exponent is even.** -/
theorem isSquare_iff_factorization_even {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    intro p
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, rfl⟩
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    have : ∀ p ∈ n.primeFactors,
        p ^ (n.factorization p / 2) * p ^ (n.factorization p / 2)
          = p ^ (n.factorization p) := by
      intro p _
      rw [← pow_add]
      congr 1
      obtain ⟨k, hk⟩ := h p
      omega
    rw [Finset.prod_congr rfl this]
    have hself := Nat.factorization_prod_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at hself
    exact hself.symm

/-- **The number of divisors is odd iff `n` is a perfect square.** The classical parity
criterion for `τ = σ₀`, the headline structural fact about the divisor-counting function. -/
theorem card_divisors_odd_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd (#n.divisors) ↔ IsSquare n := by
  rw [Nat.card_divisors hn, odd_prod_iff, isSquare_iff_factorization_even hn]
  constructor
  · intro h p
    by_cases hp : p ∈ n.primeFactors
    · have hodd := h p hp
      rw [Nat.odd_iff] at hodd
      rw [Nat.even_iff]; omega
    · have : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]; exact hp
      simp [this]
  · intro h p _
    have heven := h p
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff]; omega

/-- **σ₀ form.** Restated through Mathlib's arithmetic function `sigma 0 = τ`. -/
theorem sigma_zero_odd_iff_isSquare {n : ℕ} (hn : n ≠ 0) :
    Odd (sigma 0 n) ↔ IsSquare n := by
  rw [sigma_zero_apply]; exact card_divisors_odd_iff_isSquare hn

end SumOfDivisorsOQ06
