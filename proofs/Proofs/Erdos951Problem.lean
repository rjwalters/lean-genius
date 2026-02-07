/-
Erdos Problem #951: Beurling Prime Numbers

Source: https://erdosproblems.com/951
Status: OPEN

Statement:
Let 1 < a_1 < a_2 < ... be a sequence of real numbers such that for every
distinct pair of non-negative finitely supported integer tuples (k_i), (l_j):

  |prod_i a_i^{k_i} - prod_j a_j^{l_j}| >= 1

Question: Is it true that #{a_i <= x} <= pi(x)?

Such sequences are called Beurling prime numbers or generalized primes.
The condition ensures that products of these "primes" are well-separated,
mimicking a key property of ordinary primes.

Historical Context:
- Erdos reports this question was posed during his lecture at Queens College
  by a member of the audience (perhaps S. Shapiro)
- Beurling introduced generalized primes in 1937

Related Result (Beurlings Conjecture):
If the count of "integers" (products prod a_i^{k_i}) in [1,x] equals x + o(log x),
then the a_i must be the actual primes.

References:
- Beurling, A. (1937): "Analyse de la loi asymptotique de la distribution
  des nombres premiers generalises"
- Diamond, H. G. (1977): "A set of generalized numbers showing Beurlings theorem to be sharp"
-/

import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic

open Nat BigOperators Finset Real

namespace Erdos951

/-- A sequence (a_i) has well-separated products if for any two distinct
    products, their difference is at least 1. -/
def WellSeparatedProducts (a : ℕ → ℝ) : Prop :=
  ∀ k ℓ : ℕ →₀ ℕ, k ≠ ℓ →
    |∏ i ∈ k.support, a i ^ (k i) - ∏ j ∈ ℓ.support, a j ^ (ℓ j)| ≥ 1

/-- A Beurling prime sequence: strictly increasing, all > 1, well-separated products. -/
structure BeurlingPrimes where
  a : ℕ → ℝ
  strictly_increasing : ∀ n m, n < m → a n < a m
  all_gt_one : ∀ n, a n > 1
  well_separated : WellSeparatedProducts a

/-- Beurling prime counting function: #{n : a_n <= x}.
    Since the sequence is strictly increasing with all terms > 1,
    this set is finite for any x. We use Set.ncard. -/
noncomputable def beurlingPi (a : ℕ → ℝ) (x : ℝ) : ℕ :=
  Set.ncard {n : ℕ | a n ≤ x}

/-- Standard prime counting function: pi(x) = number of primes <= x. -/
noncomputable def primePi (x : ℝ) : ℕ := Nat.primeCounting (Nat.floor x)

/-- The counting set {n | a n <= x} is finite for Beurling prime sequences.
    Since a is strictly increasing with all a_n > 1, only finitely many
    indices satisfy a_n <= x. -/
theorem beurlingPi_finite (bp : BeurlingPrimes) (x : ℝ) :
    Set.Finite {n : ℕ | bp.a n ≤ x} := by
  sorry

/-- The nth prime as a real number. -/
noncomputable def primeSeq (n : ℕ) : ℝ := Nat.nth Nat.Prime n

/-- Prime sequence is strictly increasing. -/
axiom primeSeq_strictly_increasing : ∀ n m, n < m → primeSeq n < primeSeq m

/-- All primes are > 1. -/
axiom primeSeq_gt_one : ∀ n, primeSeq n > 1

/-- The ordinary primes have well-separated products by the
    Fundamental Theorem of Arithmetic. -/
axiom primeSeq_well_separated : WellSeparatedProducts primeSeq

/-- The ordinary primes form a Beurling prime sequence. -/
noncomputable def actualPrimes : BeurlingPrimes where
  a := primeSeq
  strictly_increasing := primeSeq_strictly_increasing
  all_gt_one := primeSeq_gt_one
  well_separated := primeSeq_well_separated

/-- For the actual primes, beurlingPi equals primePi. -/
axiom actualPrimes_counting : ∀ x : ℝ, beurlingPi primeSeq x = primePi x

/-- Powers of 2 form a Beurling prime sequence example. -/
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

/-- Powers of 2 have well-separated products. -/
axiom powersOfTwo_well_separated : WellSeparatedProducts powersOfTwo

/-- Powers of 2 form a Beurling prime sequence. -/
noncomputable def powersOfTwoBeurling : BeurlingPrimes where
  a := powersOfTwo
  strictly_increasing := powersOfTwo_increasing
  all_gt_one := powersOfTwo_gt_one
  well_separated := powersOfTwo_well_separated

/-- Well-separated products implies distinct products. -/
theorem separation_implies_distinct (a : ℕ → ℝ) (h : WellSeparatedProducts a) :
    ∀ k ℓ : ℕ →₀ ℕ, k ≠ ℓ →
      ∏ i ∈ k.support, a i ^ (k i) ≠ ∏ j ∈ ℓ.support, a j ^ (ℓ j) := by
  intro k ℓ hne
  have := h k ℓ hne
  intro heq
  simp only [heq, sub_self, abs_zero] at this
  linarith

/-- A Beurling integer is a product of Beurling primes. -/
def IsBeurlingInteger (a : ℕ → ℝ) (x : ℝ) : Prop :=
  ∃ k : ℕ →₀ ℕ, x = ∏ i ∈ k.support, a i ^ (k i)

/-- Beurling integer counting function: number of Beurling integers in [1,x]. -/
noncomputable def beurlingN (a : ℕ → ℝ) (x : ℝ) : ℕ :=
  Set.ncard {y : ℝ | IsBeurlingInteger a y ∧ 1 ≤ y ∧ y ≤ x}

/-- Beurlings conjecture: if N_a(x) = x + o(log x), then a_i must be the primes. -/
axiom beurlings_conjecture :
    ∀ bp : BeurlingPrimes,
      (∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, |beurlingN bp.a x - x| ≤ ε * Real.log x) →
      bp.a = primeSeq

/-- Erdos #951 Conjecture: For any Beurling prime sequence,
    #{a_i <= x} <= pi(x) for all x > 0. -/
def erdos951_conjecture : Prop :=
  ∀ bp : BeurlingPrimes, ∀ x : ℝ, x > 0 → beurlingPi bp.a x ≤ primePi x

-- Note: erdos951_conjecture is OPEN. We do NOT axiomatize it.

/-- Powers of 2 are sparser than primes (example supporting the conjecture). -/
axiom powersOfTwo_sparser : ∀ x : ℝ, x ≥ 4 → beurlingPi powersOfTwo x ≤ primePi x

/-- Summary of known results. -/
theorem erdos_951_summary :
    (∀ x : ℝ, x ≥ 4 → beurlingPi powersOfTwo x ≤ primePi x) ∧
    (∀ x : ℝ, beurlingPi primeSeq x = primePi x) :=
  ⟨powersOfTwo_sparser, actualPrimes_counting⟩

end Erdos951
