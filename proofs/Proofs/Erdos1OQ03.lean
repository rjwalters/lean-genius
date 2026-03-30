/-
  Erdős Problem #1, OQ-03: Conway-Guy Construction Optimality

  The Conway-Guy sequence (1968) provides the best known upper bound
  for the distinct subset sum problem. The sequence a_n satisfies:
    a_1 = 1
    a_{n+1} = ⌈(Σ_{i=1}^n a_i) / n⌉ + 1   (not quite, see below)

  More precisely, define:
    b_1 = 0, b_{n+1} = ⌈(b_n + b_{n-1} + ... + b_1 + 1) / n⌉
    a_n = b_n - b_{n-1}

  The Conway-Guy conjecture: this construction gives the minimum N
  for sets with n elements and distinct subset sums.

  Status: OPEN for n > 5 (verified computationally for small n).
-/
import Mathlib
import Proofs.Erdos1Problem

namespace Erdos1OQ03

open Finset Nat

-- ============================================================
-- Part 1: The Conway-Guy Sequence
-- ============================================================

/-- The Conway-Guy b-sequence: b_0 = 0, b_{n+1} = ⌈(sum of b_0..b_n + 1) / (n+1)⌉ -/
noncomputable def conwayGuyB : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((Finset.range (n + 1)).sum conwayGuyB + 1 + n) / (n + 1)
    -- This is ⌈(sum + 1) / (n+1)⌉ using integer division with round-up

/-- The Conway-Guy a-sequence: a_n = b_n - b_{n-1}. -/
noncomputable def conwayGuyA : ℕ → ℕ
  | 0 => 0
  | n + 1 => conwayGuyB (n + 1) - conwayGuyB n

/-- The Conway-Guy set of size n: {a_1, a_2, ..., a_n}. -/
noncomputable def conwayGuySet (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => conwayGuyA (i + 1))

/-- The maximum element of the Conway-Guy set. -/
noncomputable def conwayGuyMax (n : ℕ) : ℕ :=
  conwayGuyA n

-- ============================================================
-- Part 2: Conway-Guy Conjecture
-- ============================================================

/-- The Conway-Guy conjecture: the CG construction achieves the minimum N
    for n-element sets with distinct subset sums.

    That is, for any set A ⊆ {1,...,N} with n elements and distinct subset sums,
    N ≥ conwayGuyMax n. -/
def conwayGuyConjecture : Prop :=
  ∀ (n : ℕ), n ≥ 1 →
    ∀ (A : Finset ℕ) (N : ℕ),
      A.card = n →
      (∀ a ∈ A, a ≤ N) →
      ErdosProblem1.hasDistinctSubsetSums A →
      N ≥ conwayGuyMax n

/-- The Conway-Guy set has distinct subset sums (for all n).
    This is equivalent to the sequence being a B-sequence. -/
def conwayGuyValid : Prop :=
  ∀ (n : ℕ), n ≥ 1 →
    ErdosProblem1.hasDistinctSubsetSums (conwayGuySet n)

/-- First few values of the Conway-Guy sequence:
    a = 0, 1, 2, 3, 5, 8, 13, 21, 34, 55, ...
    (closely related to Fibonacci numbers) -/
-- Note: the actual CG sequence is 0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...
-- which differs from Fibonacci starting from the 5th term

/-- The Conway-Guy max grows as ≈ 0.22009 · 2^n. -/
def conwayGuyAsymptotic : Prop :=
  ∃ (c : ℝ), c > 0 ∧ c < 1 ∧
    ∀ (n : ℕ), n ≥ 1 →
      (conwayGuyMax n : ℝ) ≤ c * 2 ^ n

end Erdos1OQ03
