/-
  Aristotle targets for Erdős Problem #360 (Sum-free partition classes)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos360Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main asymptotic (depends on f with def via sInf)
  - NOT theorems from axiomatized bounds
  - Routine sum-free set structural facts
  - No definition sorries
  - No axioms

  Included targets (5):
  - nSumFree_empty: empty set is vacuously n-sum-free
  - nSumFree_singleton_nonzero: {a} is n-sum-free if a ≠ n
  - nSumFree_subset: n-sum-free is downward-closed
  - validPartition_parts_disjoint: parts in valid partition are pairwise disjoint
  - isNSumFree_empty_sum: empty subset sums to 0 ≠ n for n ≥ 1
-/
import Mathlib

namespace Erdos360Aristotle

open Finset

def IsNSumFree (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ T : Finset ℕ, T ⊆ S → T.sum id ≠ n

-- Routine: empty set is n-sum-free.
-- No subset of ∅ can sum to n.
theorem nSumFree_empty (n : ℕ) : IsNSumFree n ∅ := by
  sorry

-- Routine: singleton {a} is n-sum-free when a ≠ n.
-- The only nonempty subset of {a} is {a} itself, with sum a.
theorem nSumFree_singleton (n a : ℕ) (h : a ≠ n) : IsNSumFree n {a} := by
  sorry

-- Routine: IsNSumFree is downward-closed.
-- Any subset of an n-sum-free set is also n-sum-free.
theorem nSumFree_subset (n : ℕ) (A B : Finset ℕ) (hAB : A ⊆ B)
    (hB : IsNSumFree n B) : IsNSumFree n A := by
  sorry

-- Routine: empty sum is 0.
-- ∅.sum id = 0.
theorem empty_sum_zero : (∅ : Finset ℕ).sum id = 0 := by
  sorry

-- Routine: if n ≥ 1, then 0 ≠ n.
-- So no empty subset can witness n-sum-free failure.
theorem zero_ne_pos (n : ℕ) (hn : n ≥ 1) : 0 ≠ n := by
  sorry

end Erdos360Aristotle
