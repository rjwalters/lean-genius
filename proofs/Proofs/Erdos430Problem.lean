/-!
# Erdős Problem #430: Composite Numbers in Greedy Large-Factor Sequences

Erdős Problem #430 considers a greedy decreasing sequence in [1,n) defined by:
- a₁ = n - 1
- aₖ is the greatest integer in [1, aₖ₋₁) whose prime factors all exceed n - aₖ

The question asks: for sufficiently large n, must this sequence contain at
least one composite number?

Selfridge's preliminary calculations suggest yes, but no proof is known.
The problem is equivalent to the first part of Erdős Problem #385 (observed
by Sarosh Adenwalla).

Reference: https://erdosproblems.com/430
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic

/-! ## Definitions -/

/-- The smallest prime factor of n, or n itself if n ≤ 1. -/
noncomputable def minPrimeFactor (n : ℕ) : ℕ :=
  if h : 2 ≤ n then (Nat.minFac n) else n

/-- All prime factors of m exceed a given bound k. -/
def allPrimeFactorsExceed (m k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → k < p

/-- An integer m ∈ [1, n) is admissible at level n if all prime factors
    of m exceed n - m. -/
def IsAdmissible (n m : ℕ) : Prop :=
  1 ≤ m ∧ m < n ∧ allPrimeFactorsExceed m (n - m)

/-- The greedy next element: the greatest integer in [1, prev) that is
    admissible at level n. Returns 0 if no such element exists. -/
noncomputable def greedyNext (n prev : ℕ) : ℕ :=
  Finset.sup ((Finset.Icc 1 (prev - 1)).filter (fun m => decide (IsAdmissible n m) = true)) id

/-! ## The Greedy Sequence -/

/-- The greedy large-factor sequence starting from n-1.
    greedySeq n 0 = n - 1, and greedySeq n (k+1) = greedyNext n (greedySeq n k). -/
noncomputable def greedySeq (n : ℕ) : ℕ → ℕ
  | 0 => n - 1
  | k + 1 => greedyNext n (greedySeq n k)

/-- The sequence terminates at step k if greedySeq n k = 0. -/
def seqTerminates (n k : ℕ) : Prop :=
  greedySeq n k = 0

/-- The sequence contains a composite number. -/
def hasComposite (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < greedySeq n k ∧ ¬ (greedySeq n k).Prime ∧ 1 < greedySeq n k

/-! ## Example: n = 8 -/

/-- For n = 8: a₁ = 7 (prime, all factors > 8-7=1),
    a₂ = 5 (prime, all factors > 8-5=3), then sequence terminates.
    No composite appears. Small n may not have composites. -/
axiom example_n8 : greedySeq 8 0 = 7 ∧ greedySeq 8 1 = 5

/-! ## Connection to Problem #385 -/

/-- Erdős Problem #385 (first part): for large n, there exists a composite
    m < n such that all prime divisors of m exceed n - m.
    Adenwalla observed this is equivalent to Problem #430. -/
axiom erdos_385_equivalence :
  (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → hasComposite n) ↔
  (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ m : ℕ, 1 < m ∧ m < n ∧ ¬ m.Prime ∧ allPrimeFactorsExceed m (n - m))

/-! ## Main Conjecture -/

/-- Erdős Problem #430: For sufficiently large n, the greedy large-factor
    sequence starting from n-1 must contain at least one composite number.
    Selfridge's calculations support this, but no proof is known. -/
axiom erdos_430_conjecture :
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → hasComposite n

/-! ## Auxiliary: Prime Elements Dominate for Small n -/

/-- For small n, the sequence may consist entirely of primes.
    The key difficulty is showing this cannot persist for all large n. -/
axiom small_n_all_prime :
  ∃ n₀ : ℕ, ∀ n : ℕ, n ≤ n₀ →
    ∀ k : ℕ, 0 < greedySeq n k → (greedySeq n k).Prime ∨ greedySeq n k = 1
