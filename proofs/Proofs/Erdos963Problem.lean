/-
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

Axiom count: 5 (was 7; proved log_base_gap, dissociated_subset_sum_count)
Sorry count: 0

## References

- [Er65] Erdős original formulation
- [Va99, 1.22]
- <https://erdosproblems.com/963>
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A subset B of a finset A is dissociated if all subset sums are distinct.
    Equivalently, if ∑_{b ∈ S} b = ∑_{b ∈ T} b implies S = T for S, T ⊆ B. -/
def IsDissociatedSubset (A B : Finset ℝ) : Prop :=
  B ⊆ A ∧ ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T

/-- f(n): the maximum size of a dissociated subset guaranteed in any
    n-element subset of ℝ. -/
noncomputable def maxDissociatedSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B : Finset ℝ, IsDissociatedSubset A B ∧ B.card ≥ k}

/- ## Subset Sum Counting -/

/-- **PROVED** (was axiom): A dissociated set of size k has exactly 2^k
    distinct subset sums. The dissociated condition means the sum map is
    injective on the powerset, so the image has cardinality 2^|B|. -/
theorem dissociated_subset_sum_count :
  ∀ (B : Finset ℝ), (∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T) →
    (Finset.image (fun S => S.sum id) B.powerset).card = 2 ^ B.card := by
  intro B hdiss
  rw [Finset.card_image_of_injOn, Finset.card_powerset]
  intro S hS T hT heq
  exact hdiss S T (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) heq

/- ## Main Conjecture -/

/-- **Erdős's Conjecture**: f(n) ≥ ⌊log₂ n⌋ for all n ≥ 1.
    Every n-element set of reals contains a dissociated subset of size
    at least ⌊log₂ n⌋. -/
axiom erdos_963_conjecture :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 2 n

/- ## Greedy Lower Bound -/

/-- **Erdős's greedy bound**: f(n) ≥ ⌊log₃ n⌋.
    The greedy algorithm produces a dissociated subset of this size:
    at each step, a new element can be added unless all remaining elements
    are sums or differences of existing subset sums, which limits
    exclusions to at most 3^k − 1 values after choosing k elements. -/
axiom greedy_lower_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 3 n

/- ## Upper Bound -/

/-- **Trivial upper bound**: f(n) ≤ ⌊log₂ n⌋ + 1.
    A dissociated set of size k requires at least 2^k distinct subset sums,
    so k ≤ log₂(n + 1) since the sums come from an n-element ambient set. -/
axiom trivial_upper_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≤ Nat.log 2 n + 1

/- ## Structural Properties -/

/-- The empty set is trivially dissociated. -/
theorem empty_dissociated (A : Finset ℝ) : IsDissociatedSubset A ∅ := by
  constructor
  · exact Finset.empty_subset A
  · intro S T hS hT _
    rw [Finset.subset_empty] at hS hT
    rw [hS, hT]

/-- Any singleton {a} with a ≠ 0 is dissociated (subsets ∅ and {a}
    have distinct sums 0 and a). -/
theorem singleton_dissociated (A : Finset ℝ) (a : ℝ) (ha : a ∈ A) (ha0 : a ≠ 0) :
    IsDissociatedSubset A {a} := by
  constructor
  · exact Finset.singleton_subset_iff.mpr ha
  · intro S T hS hT hsum
    rw [Finset.subset_singleton_iff] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · rfl
    · simp at hsum; exfalso; exact ha0 hsum.symm
    · simp at hsum; exfalso; exact ha0 hsum
    · rfl

/-- Powers of 2 form a dissociated set (binary representation uniqueness). -/
axiom powers_of_two_dissociated :
  ∀ k : ℕ, ∀ S T : Finset ℕ,
    S ⊆ Finset.range k → T ⊆ Finset.range k →
    S.sum (fun i => (2 : ℝ) ^ i) = T.sum (fun i => (2 : ℝ) ^ i) → S = T

/-- Monotonicity: f is non-decreasing. -/
axiom maxDissociatedSize_mono :
  ∀ m n : ℕ, m ≤ n → maxDissociatedSize m ≤ maxDissociatedSize n

/-- **PROVED** (was axiom): The gap between the greedy bound and the
    conjecture: log₂ vs log₃. Since 2 ≤ 3, log₃ n ≤ log₂ n for all n. -/
theorem log_base_gap :
    ∀ n : ℕ, n ≥ 2 → Nat.log 3 n ≤ Nat.log 2 n := by
  intro n _
  apply Nat.log_anti_left <;> omega
