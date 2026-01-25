/-
Erdős Problem #891: Prime Factors in Short Intervals

Source: https://erdosproblems.com/891
Status: OPEN

Statement:
Let 2 = p₁ < p₂ < ... denote the primes and k ≥ 2.
Is it true that for all sufficiently large n, there exists an integer in
[n, n + p₁···pₖ) with more than k prime factors?

The interval length is the primorial p₁···pₖ = 2·3·5·...·pₖ.

**Known Results:**
- k = 2: The case asks if every interval of length 6 (for large n) contains
  an integer with ≥ 3 prime factors. This remains OPEN.
- Schinzel proved a weaker result: replacing p₁···pₖ with p₁···pₖ₋₁·pₖ₊₁
  (skipping pₖ), the statement holds using Pólya's theorem.
- Weisenberg showed that under Dickson's conjecture, the statement is FALSE
  if the interval length is p₁···pₖ - 1 instead of p₁···pₖ.

The problem is connected to the distribution of smooth numbers and
the density of integers with many prime factors.

References:
- Erdős-Selfridge [ErSe67, p.430]: Original problem
- Schinzel: Weaker result with modified interval
- Weisenberg: Conditional counterexample for p₁···pₖ - 1
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat BigOperators Finset

namespace Erdos891

/-
## Part I: Prime Counting and Primorials

The interval length is the primorial - the product of the first k primes.
-/

/--
**Number of prime factors (with multiplicity):**
The Ω function counts prime factors with multiplicity.
Also known as the "big omega" function.

Examples:
- Ω(12) = Ω(2² · 3) = 3
- Ω(8) = Ω(2³) = 3
- Ω(30) = Ω(2 · 3 · 5) = 3
-/
def bigOmega (n : ℕ) : ℕ := n.factorization.sum fun _ k => k

/--
**Number of distinct prime factors:**
The ω function (little omega) counts distinct prime factors.

Examples:
- ω(12) = ω(2² · 3) = 2
- ω(8) = ω(2³) = 1
- ω(30) = ω(2 · 3 · 5) = 3
-/
def littleOmega (n : ℕ) : ℕ := n.factorization.support.card

/-- For primes, Ω(p) = 1. -/
theorem bigOmega_prime (p : ℕ) (hp : p.Prime) : bigOmega p = 1 := by
  simp only [bigOmega, Nat.factorization_prime hp, Finsupp.sum_single_index]

/-- For primes, ω(p) = 1. -/
theorem littleOmega_prime (p : ℕ) (hp : p.Prime) : littleOmega p = 1 := by
  simp only [littleOmega, Nat.factorization_prime hp, Finsupp.support_single_ne_zero _ one_ne_zero,
             Finset.card_singleton]

/-- Ω(1) = 0. -/
theorem bigOmega_one : bigOmega 1 = 0 := by
  simp only [bigOmega, Nat.factorization_one, Finsupp.sum_zero_index]

/-- ω(1) = 0. -/
theorem littleOmega_one : littleOmega 1 = 0 := by
  simp only [littleOmega, Nat.factorization_one, Finsupp.support_zero, Finset.card_empty]

/-
## Part II: The k-th Prime

We use the enumeration of primes: p₁ = 2, p₂ = 3, p₃ = 5, ...
-/

/--
The n-th prime (1-indexed): prime 1 = 2, prime 2 = 3, prime 3 = 5, etc.
-/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth Nat.Prime (n - 1)

/-- The 1st prime is 2. -/
axiom nthPrime_one : nthPrime 1 = 2

/-- The 2nd prime is 3. -/
axiom nthPrime_two : nthPrime 2 = 3

/-- The 3rd prime is 5. -/
axiom nthPrime_three : nthPrime 3 = 5

/-- nthPrime k is always prime for k ≥ 1. -/
axiom nthPrime_prime (k : ℕ) (hk : k ≥ 1) : (nthPrime k).Prime

/-
## Part III: Primorial

The primorial p₁···pₖ is the product of the first k primes.
-/

/--
**Primorial** p₁···pₖ:
The product of the first k primes.

primorial(1) = 2
primorial(2) = 2 · 3 = 6
primorial(3) = 2 · 3 · 5 = 30
primorial(4) = 2 · 3 · 5 · 7 = 210
-/
noncomputable def primorial (k : ℕ) : ℕ :=
  if k = 0 then 1 else ∏ i ∈ Finset.range k, nthPrime (i + 1)

/-- primorial(1) = 2. -/
axiom primorial_one : primorial 1 = 2

/-- primorial(2) = 6. -/
axiom primorial_two : primorial 2 = 6

/-- primorial(3) = 30. -/
axiom primorial_three : primorial 3 = 30

/-- primorial(4) = 210. -/
axiom primorial_four : primorial 4 = 210

/-
## Part IV: The Main Conjecture

The problem asks if every interval [n, n + primorial(k)) for large n
contains an integer with more than k prime factors.
-/

/--
**HasManyFactors n k:**
There exists m ∈ [n, n + primorial(k)) with Ω(m) > k.
-/
def HasManyFactors (n k : ℕ) : Prop :=
  ∃ m : ℕ, n ≤ m ∧ m < n + primorial k ∧ bigOmega m > k

/--
**Erdős #891 Conjecture:**
For k ≥ 2 and all sufficiently large n, HasManyFactors n k holds.
-/
def erdos891_conjecture (k : ℕ) : Prop :=
  k ≥ 2 → ∃ N : ℕ, ∀ n ≥ N, HasManyFactors n k

/-
## Part V: The k = 2 Case

The simplest unsolved case: every interval of length 6 (for large n)
should contain an integer with ≥ 3 prime factors.
-/

/--
**k = 2 Case:**
For sufficiently large n, [n, n+6) contains an integer with Ω ≥ 3.

This is the simplest open case. Examples:
- [8, 14): 8 = 2³ has Ω(8) = 3 ✓
- [12, 18): 12 = 2² · 3 has Ω(12) = 3 ✓
- Small intervals may fail, but the conjecture is about large n.
-/
axiom erdos891_k_equals_2 : erdos891_conjecture 2

/-- 8 = 2³ has 3 prime factors (with multiplicity). -/
theorem bigOmega_eight : bigOmega 8 = 3 := by
  native_decide

/-- 12 = 2² · 3 has 3 prime factors (with multiplicity). -/
theorem bigOmega_twelve : bigOmega 12 = 3 := by
  native_decide

/-- 18 = 2 · 3² has 3 prime factors (with multiplicity). -/
theorem bigOmega_eighteen : bigOmega 18 = 3 := by
  native_decide

/-- 24 = 2³ · 3 has 4 prime factors (with multiplicity). -/
theorem bigOmega_twentyfour : bigOmega 24 = 4 := by
  native_decide

/--
Example: The interval [8, 14) satisfies the k=2 condition.
8 = 2³ has Ω(8) = 3 > 2.
-/
theorem example_interval_8_14 : HasManyFactors 8 2 := by
  use 8
  constructor
  · omega
  constructor
  · simp only [primorial_two]
    omega
  · exact bigOmega_eight ▸ (by omega : 3 > 2)

/-
## Part VI: Schinzel's Weaker Result

Schinzel proved that if we use p₁···pₖ₋₁·pₖ₊₁ instead of p₁···pₖ,
the statement holds.
-/

/--
**Modified primorial:** p₁···pₖ₋₁·pₖ₊₁ (skipping pₖ).
-/
noncomputable def primorialSkip (k : ℕ) : ℕ :=
  if k ≤ 1 then 1 else (primorial (k - 1)) * nthPrime (k + 1)

/--
**Schinzel's Theorem:**
Using primorialSkip instead of primorial, the conjecture holds.

The proof uses Pólya's theorem on gaps in k-smooth numbers.
-/
axiom schinzel_theorem (k : ℕ) (hk : k ≥ 2) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ m : ℕ, n ≤ m ∧ m < n + primorialSkip k ∧ bigOmega m > k

/-
## Part VII: Weisenberg's Conditional Counterexample

Under Dickson's conjecture, using p₁···pₖ - 1 gives a negative answer.
-/

/--
**Dickson's Conjecture (informal):**
For a finite set of linear forms aᵢn + bᵢ with aᵢ > 0,
if there is no prime p dividing ∏ᵢ(aᵢn + bᵢ) for all n,
then there are infinitely many n where all forms are prime simultaneously.

This generalizes the twin prime conjecture and many others.
-/
axiom dicksons_conjecture : Prop

/--
**Weisenberg's Observation:**
Assuming Dickson's conjecture, there exist infinitely many n such that
every integer in [n, n + primorial(k) - 1) has at most k prime factors.

This shows the interval length p₁···pₖ is critical - subtracting 1 breaks it.
-/
axiom weisenberg_conditional (k : ℕ) (hk : k ≥ 2) :
    dicksons_conjecture →
    ∃ S : Set ℕ, S.Infinite ∧ ∀ n ∈ S, ∀ m : ℕ,
      n ≤ m → m < n + primorial k - 1 → bigOmega m ≤ k

/-
## Part VIII: Smooth Numbers Connection

The problem relates to the distribution of k-smooth numbers
(numbers whose prime factors are all ≤ pₖ).
-/

/--
**k-smooth number:**
A number is k-smooth if all its prime factors are ≤ pₖ.
-/
def isSmooth (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ nthPrime k

/--
**Pólya's Theorem (informal):**
The gaps between consecutive k-smooth numbers are unbounded.

This is key to Schinzel's result.
-/
axiom polya_theorem (k : ℕ) (hk : k ≥ 1) :
    ∀ G : ℕ, ∃ n : ℕ, ∀ m : ℕ, n < m → m < n + G → ¬isSmooth m k

/-
## Part IX: Summary and Open Status
-/

/--
**Erdős Problem #891: OPEN**

Is it true that for k ≥ 2 and all sufficiently large n,
the interval [n, n + p₁···pₖ) contains an integer with > k prime factors?

Status:
- Main conjecture: OPEN
- k = 2 case: OPEN (intervals of length 6)
- Schinzel's result: Holds with p₁···pₖ₋₁·pₖ₊₁ instead
- Weisenberg: FALSE (conditionally) with p₁···pₖ - 1 instead
-/
theorem erdos_891_summary :
    (∀ k ≥ 2, erdos891_conjecture k) →  -- Full conjecture
    HasManyFactors 8 2 ∧                -- Example for k=2
    bigOmega 8 = 3 ∧                    -- 8 has 3 prime factors
    bigOmega 12 = 3 ∧                   -- 12 has 3 prime factors
    bigOmega 24 = 4 :=                  -- 24 has 4 prime factors
  fun _ => ⟨example_interval_8_14, bigOmega_eight, bigOmega_twelve, bigOmega_twentyfour⟩

/--
The main open question.
-/
axiom erdos_891 (k : ℕ) (hk : k ≥ 2) : erdos891_conjecture k

end Erdos891
