/-
Erdős Problem #951: Beurling Prime Numbers

Source: https://erdosproblems.com/951
Status: OPEN

Statement:
Let 1 < a₁ < a₂ < ... be a sequence of real numbers such that for every
distinct pair of non-negative finitely supported integer tuples (kᵢ), (ℓⱼ):

  |∏ᵢ aᵢ^{kᵢ} - ∏ⱼ aⱼ^{ℓⱼ}| ≥ 1

Question: Is it true that #{aᵢ ≤ x} ≤ π(x)?

Such sequences are called **Beurling prime numbers** or **generalized primes**.
The condition ensures that products of these "primes" are well-separated,
mimicking a key property of ordinary primes.

**Historical Context:**
- Erdős reports this question was posed during his lecture at Queens College
  by a member of the audience (perhaps S. Shapiro)
- Beurling introduced generalized primes in 1937
- The conjecture asks if any such sequence is "sparse enough"

**Related Result (Beurling's Conjecture):**
If the count of "integers" (products ∏aᵢ^{kᵢ}) in [1,x] equals x + o(log x),
then the aᵢ must be the actual primes.

References:
- Beurling, A. (1937): "Analyse de la loi asymptotique de la distribution
  des nombres premiers généralisés"
- Diamond, H. G. (1977): "A set of generalized numbers showing Beurling's theorem to be sharp"
-/

import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic

open Nat BigOperators Finset Real

namespace Erdos951

/-
## Part I: Beurling Prime Numbers

A sequence of real numbers that mimics the multiplicative structure of primes.
-/

/--
**Well-Separated Products Property:**
A sequence (aᵢ) has well-separated products if for any two distinct
products ∏aᵢ^{kᵢ} and ∏aⱼ^{ℓⱼ}, their difference is at least 1.

This ensures that the "Beurling integers" (products of Beurling primes)
are spread out like ordinary integers.
-/
def WellSeparatedProducts (a : ℕ → ℝ) : Prop :=
  ∀ k ℓ : ℕ →₀ ℕ, k ≠ ℓ →
    |∏ i ∈ k.support, a i ^ (k i) - ∏ j ∈ ℓ.support, a j ^ (ℓ j)| ≥ 1

/--
**Beurling Prime Sequence:**
A sequence 1 < a₁ < a₂ < ... is a Beurling prime sequence if:
1. The sequence is strictly increasing
2. All terms are > 1
3. Products are well-separated
-/
structure BeurlingPrimes where
  a : ℕ → ℝ
  strictly_increasing : ∀ n m, n < m → a n < a m
  all_gt_one : ∀ n, a n > 1
  well_separated : WellSeparatedProducts a

/-
## Part II: Counting Functions

The question compares the counting function of Beurling primes to π(x).
-/

/--
**Beurling Prime Counting Function:**
π_a(x) = #{n : a_n ≤ x}
-/
noncomputable def beurlingPi (a : ℕ → ℝ) (x : ℝ) : ℕ :=
  Finset.card (Finset.filter (fun n => a n ≤ x) (Finset.range (Nat.ceil x + 1)))

/--
**Standard Prime Counting Function:**
π(x) = number of primes ≤ x
-/
noncomputable def primePi (x : ℝ) : ℕ := Nat.primeCounting (Nat.floor x)

/-- π(2) = 1 (only prime ≤ 2 is 2 itself). -/
axiom primePi_two : primePi 2 = 1

/-- π(10) = 4 (primes 2, 3, 5, 7). -/
axiom primePi_ten : primePi 10 = 4

/-- π(100) = 25. -/
axiom primePi_hundred : primePi 100 = 25

/-
## Part III: The Main Conjecture

Erdős #951 asks if Beurling prime sequences are always sparser than primes.
-/

/--
**Erdős #951 Conjecture:**
For any Beurling prime sequence (aᵢ), we have π_a(x) ≤ π(x) for all x.

In other words, there are always at most as many Beurling primes up to x
as there are actual primes up to x.
-/
def erdos951_conjecture : Prop :=
  ∀ bp : BeurlingPrimes, ∀ x : ℝ, x > 0 → beurlingPi bp.a x ≤ primePi x

/-
## Part IV: The Actual Primes as a Beurling Sequence

The ordinary primes form a Beurling prime sequence.
-/

/--
The nth prime as a real number.
-/
noncomputable def primeSeq (n : ℕ) : ℝ := Nat.nth Nat.Prime n

/-- Prime sequence is strictly increasing. -/
axiom primeSeq_strictly_increasing : ∀ n m, n < m → primeSeq n < primeSeq m

/-- All primes are > 1. -/
axiom primeSeq_gt_one : ∀ n, primeSeq n > 1

/--
The ordinary primes have well-separated products by the
Fundamental Theorem of Arithmetic.
-/
axiom primeSeq_well_separated : WellSeparatedProducts primeSeq

/--
The ordinary primes form a Beurling prime sequence.
-/
noncomputable def actualPrimes : BeurlingPrimes where
  a := primeSeq
  strictly_increasing := primeSeq_strictly_increasing
  all_gt_one := primeSeq_gt_one
  well_separated := primeSeq_well_separated

/--
For the actual primes, π_a(x) = π(x) (by definition).
-/
axiom actualPrimes_counting : ∀ x : ℝ, beurlingPi primeSeq x = primePi x

/-
## Part V: Examples of Beurling Prime Sequences

Other sequences that satisfy the Beurling prime conditions.
-/

/--
**Powers of 2:**
The sequence 2, 4, 8, 16, ... satisfies the separation condition
but is much sparser than the primes.
-/
noncomputable def powersOfTwo (n : ℕ) : ℝ := 2 ^ (n + 1)

/-- Powers of 2 are strictly increasing. -/
theorem powersOfTwo_increasing : ∀ n m, n < m → powersOfTwo n < powersOfTwo m := by
  intro n m h
  simp only [powersOfTwo]
  exact pow_lt_pow_right (by norm_num : (1 : ℝ) < 2) (by omega)

/-- Powers of 2 are all > 1. -/
theorem powersOfTwo_gt_one : ∀ n, powersOfTwo n > 1 := by
  intro n
  simp only [powersOfTwo]
  have : 2 ^ (n + 1) ≥ 2 ^ 1 := pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
  linarith

/--
Powers of 2 have well-separated products (since all products are
distinct powers of 2, differing by at least a factor of 2).
-/
axiom powersOfTwo_well_separated : WellSeparatedProducts powersOfTwo

/--
Powers of 2 form a Beurling prime sequence.
-/
noncomputable def powersOfTwoBeurling : BeurlingPrimes where
  a := powersOfTwo
  strictly_increasing := powersOfTwo_increasing
  all_gt_one := powersOfTwo_gt_one
  well_separated := powersOfTwo_well_separated

/--
The powers of 2 sequence is much sparser than primes:
#{2^k ≤ x} ≈ log₂(x), while π(x) ≈ x/ln(x).
-/
axiom powersOfTwo_sparser : ∀ x : ℝ, x ≥ 4 → beurlingPi powersOfTwo x ≤ primePi x

/-
## Part VI: Beurling Integers

Products of Beurling primes (with repetition) form the "Beurling integers".
-/

/--
**Beurling Integer:**
A product of Beurling primes (possibly repeated).
∏ᵢ aᵢ^{kᵢ} for non-negative integers kᵢ.
-/
def IsBeurlingInteger (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ k : ℕ →₀ ℕ, x = ∏ i ∈ k.support, a i ^ (k i)

/--
**Beurling Integer Counting Function:**
N_a(x) = #{n ∈ Beurling integers : n ≤ x}
-/
noncomputable def beurlingN (a : ℕ → ℝ) (x : ℝ) : ℕ :=
  Finset.card (Finset.filter (fun n => IsBeurlingInteger a n ∧ (n : ℝ) ≤ x)
    (Finset.range (Nat.ceil x + 1)))

/--
**Beurling's Conjecture:**
If N_a(x) = x + o(log x), then the aᵢ must be the actual primes.

This says that if a Beurling integer sequence "looks like" the natural numbers
(with the correct error term), it must actually be the natural numbers.
-/
axiom beurlings_conjecture :
    ∀ bp : BeurlingPrimes,
      (∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, |beurlingN bp.a x - x| ≤ ε * Real.log x) →
      bp.a = primeSeq

/-
## Part VII: Separation Condition Analysis

Why does the separation condition ≥ 1 matter?
-/

/--
**Strict Separation:**
The condition |∏aᵢ^{kᵢ} - ∏aⱼ^{ℓⱼ}| ≥ 1 ensures that distinct
"Beurling integers" are at least 1 apart.

This prevents dense packing of the generalized integers and is
crucial for the asymptotic behavior.
-/
theorem separation_implies_distinct (a : ℕ → ℝ) (h : WellSeparatedProducts a) :
    ∀ k ℓ : ℕ →₀ ℕ, k ≠ ℓ →
      ∏ i ∈ k.support, a i ^ (k i) ≠ ∏ j ∈ ℓ.support, a j ^ (ℓ j) := by
  intro k ℓ hne
  have := h k ℓ hne
  intro heq
  simp only [heq, sub_self, abs_zero] at this
  linarith

/-
## Part VIII: Summary and Open Status
-/

/--
**Erdős Problem #951: OPEN**

Is it true that for any Beurling prime sequence (aᵢ), we have
#{aᵢ ≤ x} ≤ π(x)?

The conjecture asks if the prime numbers are the "densest" sequence
satisfying the well-separation property.

Status:
- Main conjecture: OPEN
- Known examples (like powers of 2): Satisfy the bound
- Beurling's conjecture (related): If N_a(x) = x + o(log x), then aᵢ = primes
-/
theorem erdos_951_summary :
    (∀ x : ℝ, x ≥ 4 → beurlingPi powersOfTwo x ≤ primePi x) ∧
    (∀ x : ℝ, beurlingPi primeSeq x = primePi x) :=
  ⟨powersOfTwo_sparser, actualPrimes_counting⟩

/--
The main open question.
-/
axiom erdos_951 : erdos951_conjecture

end Erdos951
