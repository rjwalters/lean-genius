/-
  Aristotle targets for Erdős Problem #156 (Maximal Sidon Sets of Size O(N^{1/3}))
  Supporting lemmas for automated proof search.
  See Erdos156Problem.lean for the main formalization.

  Targets:
  - diffShadow_ncard_le: |diffShadow A| ≤ |A| * (|A|*(|A|+1)/2)
    Strategy: diffShadow A ⊆ ⋃ a ∈ A, {σ - a | σ ∈ A+A, σ > a}
    Each fiber has size ≤ |A+A| = |A|*(|A|+1)/2 (by sidon_sumset_size).

  - midShadow_ncard_le: |midShadow A| ≤ |A|*(|A|+1)/2
    Strategy: midShadow A = {(b+c)/2 | b,c ∈ A, b+c even}
    This is an image of sumset A, so size ≤ |A+A| = |A|*(|A|+1)/2.

  - greedySidon_cube_lower_bound: N ≤ n + n*(n*(n+1)/2) + n*(n+1)/2
    Strategy: Interval N ⊆ greedySidon N ∪ diffShadow ∪ midShadow
    using greedySidon_complement_in_shadow. Union bound gives the result.

  Excluded:
  - The main O(N^{1/3}) conjecture (open problem)
-/
import Mathlib
import Proofs.Erdos156Problem

namespace Erdos156

/-- The diffShadow of a Sidon set A has at most |A| * (|A|*(|A|+1)/2) elements.
    Each element of diffShadow arises as σ - a for some σ ∈ sumset A and a ∈ A,
    giving a bound of |A| * |sumset A| = |A| * |A|*(|A|+1)/2. -/
lemma diffShadow_ncard_le (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (diffShadow A).ncard ≤ A.ncard * (A.ncard * (A.ncard + 1) / 2) := by
  sorry

/-- The midShadow of A has at most |A|*(|A|+1)/2 elements.
    midShadow A = {x | ∃ b c ∈ A, b + c = 2*x} ⊆ image of (sumset A) under x ↦ x/2. -/
lemma midShadow_ncard_le (A : Set ℕ) (hfin : A.Finite) :
    (midShadow A).ncard ≤ A.ncard * (A.ncard + 1) / 2 := by
  sorry

/-- The greedy Sidon set in {1,...,N} has size ≥ Ω(N^{1/3}).
    Every element of {1,...,N} not in the greedy set lies in diffShadow or midShadow
    (by greedySidon_complement_in_shadow), giving N ≤ n + shadow sizes. -/
theorem greedySidon_cube_lower_bound (N n : ℕ)
    (hn : n = size (greedySidon N)) (hN : N ≥ 1) :
    N ≤ n + n * (n * (n + 1) / 2) + n * (n + 1) / 2 := by
  sorry

end Erdos156
