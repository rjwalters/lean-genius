/-
Erdős Problem #587: Square-Sum-Free Subsets

Given N, what is the size of the largest subset A ⊆ {1,...,N} such that
for all non-empty S ⊆ A, the sum ∑_{n∈S} n is not a perfect square?

**Answer**: |A| = Θ(N^{1/3} · (log N)^{O(1)})

- Erdős observed that |A| ≥ cN^{1/3} is achievable by taking approximately N^{1/3}
  multiples of a prime p ≈ N^{2/3}.
- Nguyen and Vu (2010) proved the matching upper bound |A| ≤ C·N^{1/3}·(log N)^{O(1)}.

This problem was famously posed by Erdős to a young Terence Tao in 1985.

Reference: https://erdosproblems.com/587
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Erdos587

/-!
## Definitions

We define `MaxNotSqSum N` as the maximum cardinality of a subset A ⊆ {1,...,N}
such that no non-empty subset of A has a sum that is a perfect square.
-/

/-- A subset A is "square-sum-free" if no non-empty subset has a square sum. -/
def IsSquareSumFree (A : Finset ℕ) : Prop :=
  ∀ S ⊆ A, S.Nonempty → ¬IsSquare (∑ n ∈ S, n)

/--
`MaxNotSqSum N` is the size of the largest square-sum-free subset of {1,...,N}.

This is the central quantity in Erdős Problem #587. Erdős asked for the asymptotic
behavior of this function.
-/
noncomputable def MaxNotSqSum (N : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSquareSumFree A ∧ A.card = k }

/-!
## Main Results

The Nguyen-Vu theorem (2010) establishes that the maximum size of a square-sum-free
subset is Θ(N^{1/3} · (log N)^{O(1)}), matching Erdős's lower bound construction.
-/

/--
**Erdős's Lower Bound Construction**

Taking approximately N^{1/3} multiples of a prime p ≈ N^{2/3} gives a square-sum-free
subset of size Ω(N^{1/3}). The key insight is that sums of distinct multiples of p
are themselves multiples of p but not multiples of p², making them non-squares.

This axiom captures Erdős's constructive lower bound.
-/
axiom erdos_lower_bound : ∃ c : ℝ, c > 0 ∧
    ∀ᶠ (N : ℕ) in Filter.atTop, (MaxNotSqSum N : ℝ) ≥ c * (N : ℝ) ^ (1/3 : ℝ)

/--
**Nguyen-Vu Upper Bound (2010)**

Nguyen and Vu proved that any square-sum-free subset of {1,...,N} has size at most
O(N^{1/3} · (log N)^{O(1)}). Their proof uses methods from additive combinatorics,
including results on squares in sumsets.

Reference: "Squares in sumsets", An irregular mind (2010), pp. 491-524.

This is stated as an axiom because the full proof requires deep results from
additive combinatorics that are not yet in Mathlib.
-/
axiom nguyen_vu_upper_bound : ∃ (C : ℝ) (k : ℝ), C > 0 ∧ k > 0 ∧
    ∀ᶠ (N : ℕ) in Filter.atTop,
      (MaxNotSqSum N : ℝ) ≤ C * (N : ℝ) ^ (1/3 : ℝ) * (Real.log N) ^ k

/--
**Combined Result: Tight Asymptotic Bound**

Combining Erdős's construction and the Nguyen-Vu theorem, we have:
  MaxNotSqSum N = Θ(N^{1/3} · (log N)^{O(1)})

This shows that Erdős's simple prime-multiple construction is essentially optimal.
-/
theorem erdos_587_tight_bound : ∃ (c C : ℝ) (k : ℝ), c > 0 ∧ C > 0 ∧ k ≥ 0 ∧
    ∀ᶠ (N : ℕ) in Filter.atTop,
      c * (N : ℝ) ^ (1/3 : ℝ) ≤ (MaxNotSqSum N : ℝ) ∧
      (MaxNotSqSum N : ℝ) ≤ C * (N : ℝ) ^ (1/3 : ℝ) * (Real.log N) ^ k := by
  obtain ⟨c, hc_pos, hc_bound⟩ := erdos_lower_bound
  obtain ⟨C, k, hC_pos, hk_pos, hC_bound⟩ := nguyen_vu_upper_bound
  refine ⟨c, C, k, hc_pos, hC_pos, le_of_lt hk_pos, ?_⟩
  exact Filter.Eventually.and hc_bound hC_bound

/-!
## Concrete Examples

We verify the square-sum-free property for small examples to build intuition.
-/

/-- The empty set is trivially square-sum-free (vacuously true). -/
theorem empty_is_square_sum_free : IsSquareSumFree ∅ := by
  intro S hS hSne
  simp only [Finset.subset_empty] at hS
  exact absurd hS hSne.ne_empty

/-- A singleton {n} is square-sum-free if and only if n is not a perfect square. -/
theorem singleton_square_sum_free_iff (n : ℕ) :
    IsSquareSumFree {n} ↔ ¬IsSquare n := by
  constructor
  · intro h
    have := h {n} (Finset.Subset.refl _) (Finset.singleton_nonempty n)
    simp only [Finset.sum_singleton] at this
    exact this
  · intro hn S hS hSne
    have : S = {n} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hSne, fun x hx => Finset.mem_singleton.mp (hS hx)⟩
    rw [this, Finset.sum_singleton]
    exact hn

/-- 2 is not a perfect square. -/
theorem two_not_square : ¬IsSquare (2 : ℕ) := by
  intro ⟨k, hk⟩
  have h1 : k ≤ 1 := by
    by_contra h
    push_neg at h
    have : k * k ≥ 2 * 2 := Nat.mul_self_le_mul_self (Nat.succ_le_of_lt h)
    omega
  interval_cases k <;> omega

/-- 3 is not a perfect square. -/
theorem three_not_square : ¬IsSquare (3 : ℕ) := by
  intro ⟨k, hk⟩
  have h1 : k ≤ 1 := by
    by_contra h
    push_neg at h
    have : k * k ≥ 2 * 2 := Nat.mul_self_le_mul_self (Nat.succ_le_of_lt h)
    omega
  interval_cases k <;> omega

/-- {2} is square-sum-free since 2 is not a perfect square. -/
example : IsSquareSumFree ({2} : Finset ℕ) :=
  singleton_square_sum_free_iff 2 |>.mpr two_not_square

/-- {3} is square-sum-free since 3 is not a perfect square. -/
example : IsSquareSumFree ({3} : Finset ℕ) :=
  singleton_square_sum_free_iff 3 |>.mpr three_not_square

/-- {1, 2} is NOT square-sum-free since 1 is a perfect square (1 = 1²). -/
theorem one_two_not_square_sum_free : ¬IsSquareSumFree ({1, 2} : Finset ℕ) := by
  intro h
  have := h {1} (by decide : ({1} : Finset ℕ) ⊆ {1, 2}) (Finset.singleton_nonempty 1)
  simp only [Finset.sum_singleton] at this
  exact this ⟨1, rfl⟩

end Erdos587
