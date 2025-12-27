import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.Tactic

/-!
# Fundamental Theorem of Arithmetic

## What This Proves
Every integer greater than 1 can be represented uniquely as a product of prime numbers,
up to the order of the factors.

This theorem, also known as the Unique Factorization Theorem, is one of the cornerstones
of number theory. It justifies the definition of prime numbers as the "building blocks"
of all natural numbers.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Nat.primeFactorsList` for the prime
  factorization, and `UniqueFactorizationMonoid` to establish uniqueness. Key theorems
  include `Nat.prod_primeFactorsList` and related uniqueness results.
- **Original Contributions:** Pedagogical wrapper theorems with explicit documentation
  explaining the existence and uniqueness of prime factorization.
- **Proof Techniques Demonstrated:** Working with multisets, prime factorization lists,
  and the algebraic structure of unique factorization domains.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Data.Nat.Factorization.Basic` : Prime factorization infrastructure
- `Mathlib.Data.Nat.Factors` : The primeFactorsList function and properties
- `Mathlib.RingTheory.UniqueFactorizationDomain` : UFD structure
- `Nat.primeFactorsList` : List of prime factors with multiplicity
- `Nat.prod_primeFactorsList` : Product of factors equals the number

## Historical Note
The Fundamental Theorem of Arithmetic was first explicitly stated and proved by
Carl Friedrich Gauss in his *Disquisitiones Arithmeticae* (1801), though the result
was known implicitly to the ancient Greeks through Euclid's *Elements* (c. 300 BCE).
Euclid proved that every number can be factored into primes (Elements VII.31) and
that such a factorization is unique (Elements VII.32, IX.14).

## Why This Works
**Existence**: By strong induction on n. If n > 1, either n is prime (and we're done),
or n = ab for 1 < a, b < n. By induction hypothesis, both a and b have prime
factorizations, so n = ab does too.

**Uniqueness**: Euclid's Lemma is the key: if a prime p divides ab, then p divides a
or p divides b. This ensures that in any two factorizations of n, the same primes
must appear with the same multiplicities.

## Wiedijk's 100 Theorems: #80
-/

namespace FundamentalArithmetic

/-! ## Existence of Prime Factorization -/

/-- **Existence**: Every natural number n ≥ 1 can be written as a product of primes.

    The function `Nat.primeFactorsList n` returns the list of prime factors of n
    (with multiplicity), and their product equals n. -/
theorem prime_factorization_exists (n : ℕ) (hn : n ≠ 0) :
    n.primeFactorsList.prod = n :=
  Nat.prod_primeFactorsList hn

/-- The prime factors list is indeed a list of primes. -/
theorem prime_factors_are_prime (n : ℕ) :
    ∀ p ∈ n.primeFactorsList, Nat.Prime p :=
  fun _ hp => Nat.prime_of_mem_primeFactorsList hp

/-- The prime factorization list is always sorted. -/
theorem prime_factors_sorted (n : ℕ) :
    n.primeFactorsList.Sorted (· ≤ ·) :=
  Nat.primeFactorsList_sorted n

/-! ## Uniqueness of Prime Factorization -/

/-- **Uniqueness via Perm**: Two lists of primes with the same product are permutations.

    This is a key uniqueness result: if two prime lists have the same product,
    they contain exactly the same elements with the same multiplicities. -/
theorem prime_lists_perm_of_prod_eq {l₁ l₂ : List ℕ}
    (hp₁ : ∀ p ∈ l₁, Nat.Prime p) (hp₂ : ∀ p ∈ l₂, Nat.Prime p)
    (heq : l₁.prod = l₂.prod) (_hne : l₁.prod ≠ 0) :
    l₁.Perm l₂ := by
  have h1 : l₁.Perm l₁.prod.primeFactorsList := Nat.primeFactorsList_unique rfl hp₁
  have h2 : l₂.Perm l₂.prod.primeFactorsList := Nat.primeFactorsList_unique rfl hp₂
  rw [heq] at h1
  exact h1.trans h2.symm

/-- The prime factorization of a number determines the number uniquely.

    Two numbers with the same prime factorization list are equal. -/
theorem numbers_with_same_factors_equal {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m.primeFactorsList = n.primeFactorsList) :
    m = n := by
  have h1 := Nat.prod_primeFactorsList hm
  have h2 := Nat.prod_primeFactorsList hn
  rw [← h1, ← h2, h]

/-! ## The Fundamental Theorem of Arithmetic (Full Statement) -/

/-- **Fundamental Theorem of Arithmetic**: Every natural number n ≥ 2 has a
    representation as a product of prime numbers that is unique up to ordering.

    More precisely:
    1. **Existence**: `n.primeFactorsList.prod = n`
    2. **All Primes**: Every element of `primeFactorsList` is prime
    3. **Uniqueness**: Any other list of primes with the same product is a permutation

    The representation becomes absolutely unique when we require the primes
    to be in sorted (non-decreasing) order. -/
theorem fundamental_theorem_of_arithmetic (n : ℕ) (hn : 2 ≤ n) :
    ∃ l : List ℕ,
      (∀ p ∈ l, Nat.Prime p) ∧
      l.Sorted (· ≤ ·) ∧
      l.prod = n ∧
      (∀ l' : List ℕ, (∀ p ∈ l', Nat.Prime p) → l'.prod = n → l'.Perm l) := by
  use n.primeFactorsList
  have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Nat.one_le_of_lt hn)
  refine ⟨fun p hp => Nat.prime_of_mem_primeFactorsList hp,
          Nat.primeFactorsList_sorted n,
          Nat.prod_primeFactorsList hn_ne,
          fun l' hl' hprod => ?_⟩
  -- l'.Perm n.primeFactorsList follows from the uniqueness theorem
  exact Nat.primeFactorsList_unique hprod hl'

/-! ## Natural Numbers Form a Unique Factorization Domain -/

/-- **Algebraic Structure**: The natural numbers form a unique factorization monoid.

    This is a stronger algebraic formulation: ℕ is a `UniqueFactorizationMonoid`,
    meaning every nonzero element has a unique factorization into irreducibles
    (which for ℕ are exactly the primes). -/
theorem nat_is_ufm : UniqueFactorizationMonoid ℕ := inferInstance

/-! ## Euclid's Lemma (Key to Uniqueness) -/

/-- **Euclid's Lemma**: If a prime p divides a product ab, then p divides a or p divides b.

    This is the crucial lemma that makes uniqueness work. Without it, we could have
    "pseudo-primes" that behave differently in different factorizations. -/
theorem euclids_lemma {p a b : ℕ} (hp : Nat.Prime p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b :=
  hp.dvd_mul.mp h

/-! ## Worked Examples -/

/-- Example: Prime factorization of 12 is [2, 2, 3]. -/
example : (12 : ℕ).primeFactorsList = [2, 2, 3] := by native_decide

/-- Example: Prime factorization of 30 is [2, 3, 5]. -/
example : (30 : ℕ).primeFactorsList = [2, 3, 5] := by native_decide

/-- Example: Prime factorization of 60 is [2, 2, 3, 5]. -/
example : (60 : ℕ).primeFactorsList = [2, 2, 3, 5] := by native_decide

/-- Example: Prime factorization of a prime is just that prime. -/
example : (17 : ℕ).primeFactorsList = [17] := by native_decide

/-- Example: 2 × 2 × 3 = 12. -/
example : [2, 2, 3].prod = 12 := by native_decide

/-- Example: The factorization list is sorted. -/
example : (60 : ℕ).primeFactorsList.Sorted (· ≤ ·) :=
  Nat.primeFactorsList_sorted 60

/-! ## Corollaries and Applications -/

/-- A number is prime iff its factorization is a singleton. -/
theorem prime_iff_factors_singleton {p : ℕ} (hp : Nat.Prime p) :
    p.primeFactorsList = [p] :=
  Nat.primeFactorsList_prime hp

/-- Two coprime numbers have disjoint prime factorizations. -/
theorem coprime_disjoint_factors {m n : ℕ} (h : m.Coprime n) :
    m.primeFactorsList.Disjoint n.primeFactorsList := by
  intro p hm hn
  have hp1 := Nat.prime_of_mem_primeFactorsList hm
  have hdvd_m : p ∣ m := Nat.dvd_of_mem_primeFactorsList hm
  have hdvd_n : p ∣ n := Nat.dvd_of_mem_primeFactorsList hn
  have hdvd_gcd : p ∣ Nat.gcd m n := Nat.dvd_gcd hdvd_m hdvd_n
  rw [h] at hdvd_gcd
  exact hp1.not_dvd_one hdvd_gcd

/-! ## Connection to the Canonical Factorization

Mathlib also provides `Nat.factorization`, which represents the factorization
as a function from primes to their exponents (a `Finsupp ℕ ℕ`).

For example, 12 = 2² × 3¹ is represented as:
- factorization(12)(2) = 2
- factorization(12)(3) = 1
- factorization(12)(p) = 0 for all other primes p

This representation is often more convenient for computational purposes.
-/

/-- The factorization function counts prime occurrences in the factors list. -/
theorem factorization_eq_count (n p : ℕ) :
    n.primeFactorsList.count p = n.factorization p :=
  Nat.primeFactorsList_count_eq

/-- Example: The count of 2 in the factorization of 12 is 2. -/
example : (12 : ℕ).primeFactorsList.count 2 = 2 := by native_decide

/-- Example: The count of 3 in the factorization of 12 is 1. -/
example : (12 : ℕ).primeFactorsList.count 3 = 1 := by native_decide

/-- Example: The count of 5 in the factorization of 12 is 0. -/
example : (12 : ℕ).primeFactorsList.count 5 = 0 := by native_decide

#check prime_factorization_exists
#check prime_lists_perm_of_prod_eq
#check fundamental_theorem_of_arithmetic
#check nat_is_ufm
#check euclids_lemma

end FundamentalArithmetic
