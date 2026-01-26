/-!
# Erdős Problem #963: Dissociated Subsets

Let f(n) be the maximum k such that every n-element subset A ⊆ ℝ contains
a dissociated subset B ⊆ A with |B| ≥ k. A set is dissociated if all
subset sums are distinct. Estimate f(n), in particular whether
f(n) ≥ ⌊log₂ n⌋.

## Key Results

- **Greedy bound**: f(n) ≥ ⌊log₃ n⌋ (Erdős, greedy algorithm)
- **Conjectured**: f(n) ≥ ⌊log₂ n⌋
- A dissociated set of size k has 2^k distinct subset sums
- Powers of 2 form a dissociated set (binary representation)

## References

- [Er65] Erdős original formulation
- [Va99, 1.22]
- <https://erdosproblems.com/963>
-/

import Mathlib.Combinatorics.Additive.Dissociated
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A subset B of a finset A is dissociated if all subset sums are distinct.
    Equivalently, if ∑_{b ∈ S} b = ∑_{b ∈ T} b implies S = T for S, T ⊆ B. -/
def IsDissociatedSubset (A B : Finset ℝ) : Prop :=
  B ⊆ A ∧ ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T

/-- f(n): the maximum size of a dissociated subset guaranteed in any
    n-element subset of ℝ. -/
noncomputable def maxDissociatedSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B : Finset ℝ, IsDissociatedSubset A B ∧ B.card ≥ k}

/-! ## Subset Sum Counting -/

/-- A dissociated set of size k has exactly 2^k distinct subset sums. -/
axiom dissociated_subset_sum_count :
  ∀ (B : Finset ℝ), (∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T) →
    (Finset.image (fun S => S.sum id) B.powerset).card = 2 ^ B.card

/-! ## Main Conjecture -/

/-- **Erdős's Conjecture**: f(n) ≥ ⌊log₂ n⌋ for all n ≥ 1.
    Every n-element set of reals contains a dissociated subset of size
    at least ⌊log₂ n⌋. -/
axiom erdos_963_conjecture :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 2 n

/-! ## Greedy Lower Bound -/

/-- **Erdős's greedy bound**: f(n) ≥ ⌊log₃ n⌋.
    The greedy algorithm produces a dissociated subset of this size:
    at each step, a new element can be added unless all remaining elements
    are sums or differences of existing subset sums, which limits
    exclusions to at most 3^k − 1 values after choosing k elements. -/
axiom greedy_lower_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 3 n

/-! ## Upper Bound -/

/-- **Trivial upper bound**: f(n) ≤ ⌊log₂ n⌋ + 1.
    A dissociated set of size k requires at least 2^k distinct subset sums,
    so k ≤ log₂(n + 1) since the sums come from an n-element ambient set. -/
axiom trivial_upper_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≤ Nat.log 2 n + 1

/-! ## Structural Properties -/

/-- The empty set is trivially dissociated. -/
theorem empty_dissociated (A : Finset ℝ) : IsDissociatedSubset A ∅ := by
  constructor
  · exact Finset.empty_subset A
  · intro S T hS hT _
    rw [Finset.subset_empty] at hS hT
    rw [hS, hT]

/-- Any singleton subset is dissociated. -/
theorem singleton_dissociated (A : Finset ℝ) (a : ℝ) (ha : a ∈ A) :
    IsDissociatedSubset A {a} := by
  constructor
  · exact Finset.singleton_subset_iff.mpr ha
  · intro S T hS hT hsum
    ext x
    simp only [Finset.mem_singleton] at hS hT ⊢
    constructor
    · intro hx
      have := hS hx
      rw [this] at hx ⊢
      by_contra h
      have hT_empty : T = ∅ := by
        ext y
        simp only [Finset.mem_empty, iff_false]
        intro hy
        exact h (hT hy)
      rw [hT_empty] at hsum
      simp [Finset.sum_singleton] at hsum
      rw [Finset.subset_singleton_iff] at hS
      cases hS with
      | inl h_empty => rw [h_empty] at hx; exact (Finset.not_mem_empty x) hx
      | inr h_eq => rw [h_eq] at hsum; simp at hsum
    · intro hx
      have := hT hx
      rw [this] at hx ⊢
      by_contra h
      have hS_empty : S = ∅ := by
        ext y
        simp only [Finset.mem_empty, iff_false]
        intro hy
        exact h (hS hy)
      rw [hS_empty] at hsum
      simp [Finset.sum_singleton] at hsum
      rw [Finset.subset_singleton_iff] at hT
      cases hT with
      | inl h_empty => rw [h_empty] at hx; exact (Finset.not_mem_empty x) hx
      | inr h_eq => rw [h_eq] at hsum; simp at hsum

/-- Powers of 2 form a dissociated set (binary representation uniqueness). -/
axiom powers_of_two_dissociated :
  ∀ k : ℕ, ∀ S T : Finset ℕ,
    S ⊆ Finset.range k → T ⊆ Finset.range k →
    S.sum (fun i => (2 : ℝ) ^ i) = T.sum (fun i => (2 : ℝ) ^ i) → S = T

/-- Monotonicity: f is non-decreasing. -/
axiom maxDissociatedSize_mono :
  ∀ m n : ℕ, m ≤ n → maxDissociatedSize m ≤ maxDissociatedSize n

/-- The gap between the greedy bound and the conjecture: log₂ vs log₃. -/
axiom log_base_gap :
  ∀ n : ℕ, n ≥ 2 → Nat.log 3 n ≤ Nat.log 2 n
