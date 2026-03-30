/-
  Aristotle targets for Erdős Problem #1, Open Question 03
  Routine supporting lemmas for automated proof search.
  See Erdos1OQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result (binary representation uniqueness)
  - Clean theorem statement with no definition sorries
  - No axioms
-/
import Proofs.Erdos1Problem
import Proofs.Erdos1OQ01
import Mathlib

open Finset

namespace ConwayGuy

/-- ∑_{i=0}^{n-1} 2^i + 1 = 2^n -/
theorem geom_sum_two' (n : ℕ) :
    ∑ i in Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ, two_mul]
    omega

/-- Any subset of {0,...,n-1} has power-of-2 sum ≤ 2^n - 1. -/
theorem subset_pow_two_sum_le' {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range n) :
    S.sum (2 ^ ·) ≤ 2 ^ n - 1 := by
  have h1 : S.sum (2 ^ ·) ≤ (Finset.range n).sum (2 ^ ·) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have h2 := geom_sum_two' n
  omega

/-- Binary representation uniqueness: distinct subsets of {0,...,n-1}
    have distinct power-of-2 sums. By induction on n. -/
theorem pow_two_sum_injective (n : ℕ) :
    ∀ S T : Finset ℕ, S ⊆ Finset.range n → T ⊆ Finset.range n →
    S.sum (2 ^ ·) = T.sum (2 ^ ·) → S = T := by
  sorry

end ConwayGuy
