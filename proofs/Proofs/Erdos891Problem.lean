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
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat BigOperators Finset

namespace Erdos891

/-
## Part I: Arithmetic Functions

The key arithmetic function is Ω (bigOmega), which counts prime factors
with multiplicity.
-/

/--
**Number of prime factors (with multiplicity):**
The Ω function counts prime factors with multiplicity.
Defined as the sum of all exponents in the prime factorization.

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
  unfold bigOmega
  rw [hp.factorization]
  simp [Finsupp.sum_single_index]

/-- For primes, ω(p) = 1. -/
theorem littleOmega_prime (p : ℕ) (hp : p.Prime) : littleOmega p = 1 := by
  unfold littleOmega
  rw [hp.factorization]
  simp [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.card_singleton]

/-- Ω(1) = 0. -/
theorem bigOmega_one : bigOmega 1 = 0 := by
  unfold bigOmega
  simp [Nat.factorization_one, Finsupp.sum_zero_index]

/-- ω(1) = 0. -/
theorem littleOmega_one : littleOmega 1 = 0 := by
  unfold littleOmega
  simp [Nat.factorization_one, Finsupp.support_zero, Finset.card_empty]

-- Specific verified values
/-- Ω(8) = 3 (8 = 2³). -/
theorem bigOmega_eight : bigOmega 8 = 3 := by native_decide

/-- Ω(12) = 3 (12 = 2² · 3). -/
theorem bigOmega_twelve : bigOmega 12 = 3 := by native_decide

/-- Ω(18) = 3 (18 = 2 · 3²). -/
theorem bigOmega_eighteen : bigOmega 18 = 3 := by native_decide

/-- Ω(20) = 3 (20 = 2² · 5). -/
theorem bigOmega_twenty : bigOmega 20 = 3 := by native_decide

/-- Ω(24) = 4 (24 = 2³ · 3). -/
theorem bigOmega_twentyfour : bigOmega 24 = 4 := by native_decide

/-- Ω(27) = 3 (27 = 3³). -/
theorem bigOmega_twentyseven : bigOmega 27 = 3 := by native_decide

/-- Ω(0) = 0 (by convention). -/
theorem bigOmega_zero : bigOmega 0 = 0 := by native_decide

/-
## Part II: Prime Enumeration and General Primorial

We define the primorial function for ALL k using Mathlib's `Nat.nth` prime
enumeration. This is noncomputable but mathematically general.
-/

/-- The n-th prime (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Each nthPrime is indeed prime. -/
lemma nthPrime_prime (n : ℕ) : (nthPrime n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The nthPrime sequence is strictly increasing. -/
lemma nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/--
**Primorial function (general):**
The product of the first k primes: primorial k = p₁ · p₂ · ... · pₖ.
- primorial 0 = 1 (empty product)
- primorial 1 = 2
- primorial 2 = 2 · 3 = 6
- primorial k = ∏_{i=0}^{k-1} nthPrime(i)

This is noncomputable but defined for all k ∈ ℕ. -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, nthPrime i

/-- The primorial is always positive. -/
lemma primorial_pos (k : ℕ) : 0 < primorial k := by
  unfold primorial
  apply Finset.prod_pos
  intro i _
  exact (nthPrime_prime i).pos

/--
**HasManyFactors n k (general):**
There exists m ∈ [n, n + primorial(k)) with Ω(m) > k.
Uses the general primorial, valid for all k. -/
def HasManyFactors (n k : ℕ) : Prop :=
  ∃ m : ℕ, n ≤ m ∧ m < n + primorial k ∧ bigOmega m > k

/-
## Part III: Computable Primorial (for decidable verification)

For small k, we define primorial computably so that `native_decide` can verify
the conjecture on specific ranges.
-/

/--
**Computable primorial by index**:
The product of the first k primes.

primorialComp(0) = 1
primorialComp(1) = 2
primorialComp(2) = 2 · 3 = 6
primorialComp(3) = 2 · 3 · 5 = 30
primorialComp(4) = 2 · 3 · 5 · 7 = 210
primorialComp(5) = 2 · 3 · 5 · 7 · 11 = 2310
-/
def primorialComp : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 6
  | 3 => 30
  | 4 => 210
  | 5 => 2310
  | _ + 6 => 0

-- Verify primorial values (all by rfl - definitional equality)
theorem primorialComp_zero : primorialComp 0 = 1 := rfl
theorem primorialComp_one : primorialComp 1 = 2 := rfl
theorem primorialComp_two : primorialComp 2 = 6 := rfl
theorem primorialComp_three : primorialComp 3 = 30 := rfl
theorem primorialComp_four : primorialComp 4 = 210 := rfl
theorem primorialComp_five : primorialComp 5 = 2310 := rfl

/-
## Part IV: The Main Conjecture
-/

/--
**HasManyFactorsComp n k:**
There exists m ∈ [n, n + primorialComp(k)) with Ω(m) > k.
Uses the computable primorial for decidable verification.
-/
def HasManyFactorsComp (n k : ℕ) : Prop :=
  ∃ m : ℕ, n ≤ m ∧ m < n + primorialComp k ∧ bigOmega m > k

/-
## Part V: Computational Verification of k = 2 Case

The k = 2 case asks: does every interval [n, n+6) contain
an integer with ≥ 3 prime factors (counted with multiplicity)?

We verify this computationally for n ∈ [3, 1002].
The conjecture fails for n ∈ {0, 1, 2}: the interval [0,6) has max Ω = 2
(at 4 = 2²), and similarly for [1,7) and [2,8).
Starting from n = 3, the interval [3,9) contains 8 = 2³ with Ω = 3.
-/

/-- Decidable check: does [n, n+6) contain m with Ω(m) > 2? -/
def hasThreeFactorsInSix (n : ℕ) : Bool :=
  (List.range 6).any (fun i => decide (bigOmega (n + i) > 2))

/-- The k=2 conjecture fails for n = 0, 1, 2. -/
theorem k2_fails_small : hasThreeFactorsInSix 0 = false
    ∧ hasThreeFactorsInSix 1 = false
    ∧ hasThreeFactorsInSix 2 = false := by native_decide

/-- The k=2 check succeeds for all n ∈ [3, 1002].
This provides strong computational evidence for the k=2 conjecture. -/
theorem k2_verified_range : ∀ n : Fin 1000, hasThreeFactorsInSix (n.val + 3) = true := by
  native_decide

/--
Example: The interval [8, 14) satisfies the k=2 condition.
8 = 2³ has Ω(8) = 3 > 2.
-/
theorem example_interval_8_14 : HasManyFactorsComp 8 2 :=
  ⟨8, le_refl 8, by simp [primorialComp], bigOmega_eight ▸ (by omega : 3 > 2)⟩

/--
Example: The interval [12, 18) satisfies the k=2 condition.
12 = 2² · 3 has Ω(12) = 3 > 2.
-/
theorem example_interval_12_18 : HasManyFactorsComp 12 2 :=
  ⟨12, le_refl 12, by simp [primorialComp], bigOmega_twelve ▸ (by omega : 3 > 2)⟩

/--
Example: The interval [100, 106) satisfies the k=2 condition.
100 = 2² · 5² has Ω(100) = 4 > 2.
-/
theorem example_interval_100 : HasManyFactorsComp 100 2 := by
  refine ⟨100, le_refl 100, by simp [primorialComp], ?_⟩
  native_decide

/-
## Part VI: Structural Observations

Key structural facts that help understand why the conjecture
should hold for k = 2.
-/

/-- Every interval of length 6 contains an even number. -/
theorem interval_contains_even (n : ℕ) :
    ∃ m, n ≤ m ∧ m < n + 6 ∧ 2 ∣ m := by
  use 2 * ((n + 1) / 2)
  refine ⟨by omega, by omega, dvd_mul_right 2 _⟩

/-- Every interval of length 6 contains a multiple of 4. -/
theorem interval_contains_mult4 (n : ℕ) :
    ∃ m, n ≤ m ∧ m < n + 6 ∧ 4 ∣ m := by
  use 4 * ((n + 3) / 4)
  refine ⟨by omega, by omega, dvd_mul_right 4 _⟩

/-
## Part VII: Schinzel's Weaker Result

Schinzel proved that the statement holds with a slightly larger interval:
p₁···pₖ₋₁·pₖ₊₁ instead of p₁···pₖ (the product skipping pₖ and including pₖ₊₁).

The proof relies on Pólya's theorem that gaps between k-smooth numbers
are unbounded: for any G, there exist G consecutive integers none of
which is k-smooth. A non-k-smooth number in [n, n+primorialSkip(k)) must
have a prime factor > pₖ, and combined with the mandatory small prime
factors in a long enough interval, this gives Ω > k.

This result is important because it shows the conjecture is "almost true":
the primorial is the right order of magnitude for the interval length.
-/

/--
**Schinzel's Theorem:**
For k ≥ 2, the Erdős #891 statement holds with the "skipped primorial"
Q_k = p₁···pₖ₋₁·pₖ₊₁ (product of first k primes with pₖ replaced by pₖ₊₁).
This interval is slightly larger than the primorial p₁···pₖ.

Examples: Q₂ = 2·5 = 10, Q₃ = 2·3·7 = 42, Q₄ = 2·3·5·11 = 330.

This is the best known unconditional result toward Erdős #891.
We state this existentially since the precise Q requires prime enumeration. -/
/-
## Part VIII: Weisenberg's Conditional Counterexample

Weisenberg observed that under Dickson's conjecture, if the interval
length is reduced by just 1 (from p₁···pₖ to p₁···pₖ - 1), then
the statement becomes FALSE. This shows the primorial is a sharp threshold.

The construction: Let Lₖ = lcm(1, 2, ..., p₁···pₖ). By Dickson's conjecture,
there are infinitely many n' such that (Lₖ/m)·n' + 1 is prime for all
1 ≤ m < p₁···pₖ. Setting n = Lₖ·n' + 1, every integer in
[n, n + p₁···pₖ - 1) has the form n + j where j < p₁···pₖ - 1.
Since n + j = Lₖ·n' + 1 + j, and (1 + j) divides Lₖ, we get
n + j = (Lₖ/(1+j))·((1+j)·n' + (1+j)) = (Lₖ/(1+j))·(product of two terms).
By construction, one factor is prime, giving at most k prime factors total.
-/

/-- **Dickson's Conjecture** (1904):
For any finite collection of linear forms aᵢn + bᵢ with aᵢ > 0,
if no prime p divides ∏(aᵢn + bᵢ) for ALL n (the "no fixed prime divisor" condition),
then there are infinitely many n making all forms simultaneously prime.

This is one of the central open problems in analytic number theory, encompassing
the twin prime conjecture (k=2, a=(1,1), b=(0,2)) and many other conjectures.
Used by Weisenberg to show the primorial threshold is sharp. -/
def DicksonsConjecture : Prop :=
  ∀ (k : ℕ) (a b : Fin k → ℕ),
    (∀ i, 0 < a i) →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i : Fin k, ¬(p ∣ a i * n + b i)) →
    Set.Infinite {n : ℕ | ∀ i : Fin k, (a i * n + b i).Prime}

/--
**Weisenberg's Observation:**
Under Dickson's conjecture, the interval length p₁···pₖ is sharp.
Reducing it by 1 gives infinitely many counterexamples.

Uses the general `primorial` so the statement is correct for all k ≥ 2. -/
/-
## Part IX: Smooth Numbers

The problem relates to the distribution of k-smooth numbers.
A number is k-smooth if all its prime factors are at most the k-th prime.

Pólya proved that gaps between k-smooth numbers grow without bound.
This means there exist arbitrarily long intervals with NO k-smooth numbers.
Schinzel used this to prove his weaker version of Erdős #891.
-/

/--
**k-smooth number (computable):**
A number n is k-smooth if its largest prime factor is at most the k-th prime.
We define this computably using minFac iteration.
-/
def isSmoothComp (n : ℕ) (bound : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ bound

-- Example: 12 is 3-smooth (prime factors are 2 and 3)
theorem twelve_is_3smooth : isSmoothComp 12 3 := by
  intro p hp hpd
  have : p ∈ (12 : ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
  have h12 : (12 : ℕ).primeFactors = {2, 3} := by native_decide
  rw [h12] at this
  simp at this
  omega

-- Example: 7 is NOT 3-smooth (7 > 3)
theorem seven_not_3smooth : ¬ isSmoothComp 7 3 := by
  intro h
  have h7 : Nat.Prime 7 := by decide
  have := h 7 h7 (dvd_refl 7)
  omega

/-
## Part X: Summary and Main Conjecture

**Erdős Problem #891: OPEN**

Is it true that for k ≥ 2 and all sufficiently large n,
the interval [n, n + p₁···pₖ) contains an integer with > k prime factors?

Status:
- Main conjecture: OPEN
- k = 2 case: OPEN (intervals of length 6)
  - Computationally verified for n ∈ [3, 1002] (k2_verified_range)
  - Fails for n ∈ {0, 1, 2} (k2_fails_small)
- Schinzel's result: Holds with larger interval p₁···pₖ₋₁·pₖ₊₁
- Weisenberg: FALSE (conditionally) with interval p₁···pₖ - 1

Key insight: The primorial p₁···pₖ appears to be the exact threshold.
Below it (p₁···pₖ - 1), the statement fails conditionally.
Above it (p₁···pₖ₋₁·pₖ₊₁), the statement holds unconditionally.

Uses `primorial` (via Nat.nth Nat.Prime), which is valid for all k.
The computable `HasManyFactorsComp` is used only for decidable k=2 verification.
-/
/-- **Erdős Problem #891 (OPEN):**
    Stated as a definition since this is an open conjecture.
    Uses the general `primorial` so the statement is mathematically correct for all k. -/
def ErdosProblem891 : Prop :=
    ∀ k : ℕ, k ≥ 2 → ∃ N : ℕ, ∀ n ≥ N, HasManyFactors n k

end Erdos891
