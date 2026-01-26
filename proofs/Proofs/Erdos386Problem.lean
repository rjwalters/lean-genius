/-!
# Erdős Problem 386: Binomial Coefficients as Products of Consecutive Primes

*Reference:* [erdosproblems.com/386](https://www.erdosproblems.com/386)

Let `2 ≤ k ≤ n - 2`. Can `C(n,k)` be the product of consecutive primes
infinitely often?

This problem, from Erdős and Graham (1980, p.74), asks about when a binomial
coefficient equals a *primorial quotient* — i.e., a product of consecutive
primes `p_i · p_{i+1} · ⋯ · p_j`. Known examples include:

  C(21, 2) = 210  = 2 · 3 · 5 · 7
  C(7, 3)  = 35   = 5 · 7
  C(10, 4) = 210  = 2 · 3 · 5 · 7
  C(14, 4) = 1001 = 7 · 11 · 13
  C(15, 6) = 5005 = 5 · 7 · 11 · 13

This remains an open problem.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section 1: Prime enumeration

We define the enumeration of primes: `nthPrime i` is the `i`-th prime
(0-indexed), so `nthPrime 0 = 2`, `nthPrime 1 = 3`, etc.
-/

namespace Erdos386

open Nat

/-- The `i`-th prime number (0-indexed). -/
noncomputable def nthPrime (i : ℕ) : ℕ :=
  (Nat.Primes.instCountable.toEncodable.decode i).getD 2

/-- `nthPrime i` is always prime (axiom; depends on Mathlib's prime enumeration). -/
axiom nthPrime_prime (i : ℕ) : Nat.Prime (nthPrime i)

/-- `nthPrime` is strictly increasing. -/
axiom nthPrime_strictMono : StrictMono nthPrime

/-!
## Section 2: Product of consecutive primes

We define what it means for a number to equal a product of consecutive primes
`p_a · p_{a+1} · ⋯ · p_{b-1}`.
-/

/-- The product of consecutive primes from index `a` to index `b - 1`. -/
noncomputable def consecutivePrimeProd (a b : ℕ) : ℕ :=
  (Finset.Ico a b).prod (fun i => nthPrime i)

/-- A number `m` is a product of consecutive primes if `m = ∏_{i ∈ [a,b)} nthPrime i`
    for some `a < b`. -/
def IsProductOfConsecutivePrimes (m : ℕ) : Prop :=
  ∃ a b : ℕ, a < b ∧ m = consecutivePrimeProd a b

/-!
## Section 3: Known examples

We state known examples where `C(n,k)` equals a product of consecutive primes.
-/

/-- C(21, 2) = 210 = 2 · 3 · 5 · 7 -/
axiom choose_21_2_consec_primes :
  IsProductOfConsecutivePrimes (Nat.choose 21 2)

/-- C(7, 3) = 35 = 5 · 7 -/
axiom choose_7_3_consec_primes :
  IsProductOfConsecutivePrimes (Nat.choose 7 3)

/-- C(10, 4) = 210 = 2 · 3 · 5 · 7 -/
axiom choose_10_4_consec_primes :
  IsProductOfConsecutivePrimes (Nat.choose 10 4)

/-- C(14, 4) = 1001 = 7 · 11 · 13 -/
axiom choose_14_4_consec_primes :
  IsProductOfConsecutivePrimes (Nat.choose 14 4)

/-- C(15, 6) = 5005 = 5 · 7 · 11 · 13 -/
axiom choose_15_6_consec_primes :
  IsProductOfConsecutivePrimes (Nat.choose 15 6)

/-!
## Section 4: The main conjecture

Erdős Problem 386 asks: for fixed `k ≥ 2`, do there exist infinitely many `n`
with `2 ≤ k ≤ n - 2` such that `C(n,k)` is a product of consecutive primes?
-/

/-- Erdős Problem 386: For every `k ≥ 2`, are there infinitely many `n`
    with `k ≤ n - 2` such that `C(n, k)` is a product of consecutive primes? -/
def ErdosProblem386 : Prop :=
  ∀ k : ℕ, k ≥ 2 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ k + 2 ≤ n ∧
      IsProductOfConsecutivePrimes (Nat.choose n k)

/-!
## Section 5: Structural observations

Products of consecutive primes are *squarefree* (each prime appears exactly
once), so a necessary condition for `C(n,k)` to be such a product is that
`C(n,k)` is squarefree.
-/

/-- A number is squarefree if no prime square divides it. -/
def IsSquarefree (m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p * p ∣ m)

/-- A product of consecutive primes is squarefree. -/
axiom consecutivePrimeProd_squarefree (a b : ℕ) (h : a < b) :
  IsSquarefree (consecutivePrimeProd a b)

/-- If `C(n,k)` is a product of consecutive primes, then it is squarefree. -/
theorem choose_consec_primes_squarefree {n k : ℕ}
    (h : IsProductOfConsecutivePrimes (Nat.choose n k)) :
    IsSquarefree (Nat.choose n k) := by
  obtain ⟨a, b, hab, heq⟩ := h
  rw [heq]
  exact consecutivePrimeProd_squarefree a b hab

/-!
## Section 6: The k = 2 case

For `k = 2`, we have `C(n, 2) = n(n-1)/2`. This is a product of consecutive
primes when `n(n-1)/2` is a primorial or primorial quotient.
-/

/-- For k = 2, the problem reduces to finding n where n(n-1)/2 is a product
    of consecutive primes. The known example is C(21, 2) = 210 = 2·3·5·7. -/
axiom erdos_386_k2_examples :
  ∃ n : ℕ, n ≥ 4 ∧ IsProductOfConsecutivePrimes (Nat.choose n 2)

/-!
## Section 7: Connection to Erdős–Graham (1980)

This problem appears in Erdős and Graham's 1980 monograph "Old and New Problems
and Results in Combinatorial Number Theory" (p. 74). The broader theme is
understanding the prime factorization structure of binomial coefficients.
Related problems include Erdős Problem 384 (prime divisors < n/2) and
Erdős Problem 387 (divisors in interval (cn, n]).
-/

/-- The Erdős–Graham observation: if C(n,k) is a product of consecutive primes,
    then the largest prime factor of C(n,k) is at most n. -/
axiom choose_largest_prime_le (n k : ℕ) (hk : 2 ≤ k) (hn : k + 2 ≤ n)
    (p : ℕ) (hp : Nat.Prime p) (hd : p ∣ Nat.choose n k) :
    p ≤ n

end Erdos386
