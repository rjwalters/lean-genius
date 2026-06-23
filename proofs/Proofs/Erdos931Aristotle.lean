/-
  Aristotle targets for Erdős Problem #931
  Routine supporting lemmas for automated proof search.
  See Erdos931Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (ErdosProblem931, StrongerConjecture)
  - NOT the smooth-number-theory reductions (stronger_implies_main,
    exists_prime_between_blocks_hard) — these depend on Mathlib infra
    that does not yet exist (Stoermer's theorem, smooth-number bounds)
  - Routine supporting facts about consecutiveProduct and
    consecutivePrimeFactors that are derivable from existing
    Mathlib lemmas
  - No definition sorries
  - No axioms
-/
import Proofs.Erdos931Problem
import Mathlib

namespace Erdos931Aristotle

open Erdos931 Nat Finset

/-- Recurrence: extending the block by one factor multiplies the product
    by the new endpoint `n + k + 1`. Follows from `Finset.prod_Icc_succ_top`. -/
theorem consecutiveProduct_succ (n k : ℕ) :
    consecutiveProduct n (k + 1) = consecutiveProduct n k * (n + (k + 1)) := by
  sorry

/-- The product over a shorter block divides the product over a longer block.
    Direct corollary of `consecutiveProduct_succ` by induction on `k₂ - k₁`. -/
theorem consecutiveProduct_dvd_of_le (n k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    consecutiveProduct n k₁ ∣ consecutiveProduct n k₂ := by
  sorry

/-- Prime factors are monotone in `k`: extending the block only adds
    prime factors. Follows from `consecutiveProduct_dvd_of_le` and
    `Nat.primeFactors_mono` (the divisibility version). -/
theorem consecutivePrimeFactors_mono_k (n k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    consecutivePrimeFactors n k₁ ⊆ consecutivePrimeFactors n k₂ := by
  sorry

/-- For `k ≥ 3`, the prime `3` is always a factor: at least one of
    `n+1, n+2, n+3` is divisible by `3`. Specializes
    `Erdos931.prime_le_k_mem_factors` to `p = 3`. -/
theorem three_mem_factors (n k : ℕ) (hk : 3 ≤ k) :
    3 ∈ consecutivePrimeFactors n k :=
  prime_le_k_mem_factors n k 3 (by decide) hk

/-- For `k ≥ 5`, the prime `5` is always a factor. -/
theorem five_mem_factors (n k : ℕ) (hk : 5 ≤ k) :
    5 ∈ consecutivePrimeFactors n k :=
  prime_le_k_mem_factors n k 5 (by decide) hk

/-- Every prime factor of the consecutive product is at most `n + k`,
    since each prime divides some factor `n + i` with `1 ≤ i ≤ k`,
    and divisibility implies the prime is no larger than the dividend. -/
theorem consecutivePrimeFactors_le (n k p : ℕ)
    (hp : p ∈ consecutivePrimeFactors n k) : p ≤ n + k := by
  sorry

/-- If two blocks share the same prime factors, then any prime dividing
    one of the second-block factors divides one of the first-block factors.
    Direct restatement of `SamePrimeFactors` in dvd form. -/
theorem samePrimeFactors_transfer
    {n₁ k₁ n₂ k₂ : ℕ} (h : SamePrimeFactors n₁ k₁ n₂ k₂)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ consecutiveProduct n₂ k₂) :
    p ∣ consecutiveProduct n₁ k₁ := by
  sorry

/-- The empty block (k = 0) has no prime factors. -/
theorem consecutivePrimeFactors_zero (n : ℕ) :
    consecutivePrimeFactors n 0 = ∅ := by
  sorry

end Erdos931Aristotle
