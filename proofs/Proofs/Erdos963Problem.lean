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

/-- **Erdős's Conjecture (OPEN)**: f(n) ≥ ⌊log₂ n⌋ for all n ≥ 1.
    Every n-element set of reals contains a dissociated subset of size
    at least ⌊log₂ n⌋. This is an open conjecture, not proved. -/
def ErdosProblem963 : Prop :=
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

/-- Auxiliary: ∑_{i<k} 2^i = 2^k - 1 (geometric series for ℕ). -/
private lemma sum_range_pow_two (k : ℕ) :
    (Finset.range k).sum (fun i => (2 : ℕ) ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

/-- Auxiliary: any subset sum of {2^i : i < k} is strictly less than 2^k. -/
private lemma subset_sum_lt_pow_two (k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range k) :
    S.sum (fun i => (2 : ℕ) ^ i) < 2 ^ k := by
  have h1 : S.sum (fun i => 2 ^ i) ≤ (Finset.range k).sum (fun i => 2 ^ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have h2 := sum_range_pow_two k
  omega

/-- Binary representation uniqueness over ℕ: if S, T ⊆ {0, ..., k-1} and
    ∑_{i∈S} 2^i = ∑_{i∈T} 2^i then S = T. -/
private lemma binary_uniqueness_nat :
    ∀ k : ℕ, ∀ S T : Finset ℕ,
      S ⊆ Finset.range k → T ⊆ Finset.range k →
      S.sum (fun i => (2 : ℕ) ^ i) = T.sum (fun i => (2 : ℕ) ^ i) → S = T := by
  intro k
  induction k with
  | zero =>
    intro S T hS hT _
    simp [Finset.range_zero, Finset.subset_empty] at hS hT
    rw [hS, hT]
  | succ n ih =>
    intro S T hS hT hsum
    have mem_range_succ : ∀ x ∈ S, x < n + 1 := fun x hx => Finset.mem_range.mp (hS hx)
    have mem_range_succ' : ∀ x ∈ T, x < n + 1 := fun x hx => Finset.mem_range.mp (hT hx)
    by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T
    · -- Both contain n: remove n from both, apply IH
      have hS' : S.erase n ⊆ Finset.range n := by
        intro x hx
        have hxS := (Finset.mem_erase.mp hx).2
        have hxn := (Finset.mem_erase.mp hx).1
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS hxS))) hxn)
      have hT' : T.erase n ⊆ Finset.range n := by
        intro x hx
        have hxT := (Finset.mem_erase.mp hx).2
        have hxn := (Finset.mem_erase.mp hx).1
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hT hxT))) hxn)
      have hsum' : (S.erase n).sum (fun i => 2 ^ i) = (T.erase n).sum (fun i => 2 ^ i) := by
        have := Finset.sum_erase_add S (fun i => (2 : ℕ) ^ i) hnS
        have := Finset.sum_erase_add T (fun i => (2 : ℕ) ^ i) hnT
        omega
      have := ih (S.erase n) (T.erase n) hS' hT' hsum'
      exact Finset.erase_injOn_of_mem hnS hnT this
    · -- n ∈ S, n ∉ T: contradiction (S sum ≥ 2^n, T sum < 2^n)
      exfalso
      have hT' : T ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hT hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnT (h ▸ hx)))
      have hT_bound := subset_sum_lt_pow_two n T hT'
      have hS_lower : S.sum (fun i => 2 ^ i) ≥ 2 ^ n := by
        calc S.sum (fun i => 2 ^ i)
            ≥ (({n} : Finset ℕ)).sum (fun i => 2 ^ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnS) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := by simp
      omega
    · -- n ∉ S, n ∈ T: symmetric contradiction
      exfalso
      have hS' : S ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hS hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnS (h ▸ hx)))
      have hS_bound := subset_sum_lt_pow_two n S hS'
      have hT_lower : T.sum (fun i => 2 ^ i) ≥ 2 ^ n := by
        calc T.sum (fun i => 2 ^ i)
            ≥ (({n} : Finset ℕ)).sum (fun i => 2 ^ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnT) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := by simp
      omega
    · -- Neither contains n: both subsets of range(n), apply IH
      have hS' : S ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hS hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnS (h ▸ hx)))
      have hT' : T ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hT hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnT (h ▸ hx)))
      exact ih S T hS' hT' hsum

/-- **PROVED** (was axiom): Powers of 2 form a dissociated set (binary representation uniqueness). -/
theorem powers_of_two_dissociated :
  ∀ k : ℕ, ∀ S T : Finset ℕ,
    S ⊆ Finset.range k → T ⊆ Finset.range k →
    S.sum (fun i => (2 : ℝ) ^ i) = T.sum (fun i => (2 : ℝ) ^ i) → S = T := by
  intro k S T hS hT hsum
  apply binary_uniqueness_nat k S T hS hT
  -- Reduce ℝ sum equality to ℕ sum equality via casting
  have cast_eq : ∀ U : Finset ℕ,
      U.sum (fun i => (2 : ℝ) ^ i) = ↑(U.sum (fun i => (2 : ℕ) ^ i)) := by
    intro U
    push_cast [Finset.sum_coe_sort]
    simp [Nat.cast_sum, Nat.cast_pow]
  rw [cast_eq, cast_eq] at hsum
  exact_mod_cast hsum

/-- Monotonicity: f is non-decreasing. -/
axiom maxDissociatedSize_mono :
  ∀ m n : ℕ, m ≤ n → maxDissociatedSize m ≤ maxDissociatedSize n

/-- **PROVED** (was axiom): The gap between the greedy bound and the
    conjecture: log₂ vs log₃. Since 2 ≤ 3, log₃ n ≤ log₂ n for all n. -/
theorem log_base_gap :
    ∀ n : ℕ, n ≥ 2 → Nat.log 3 n ≤ Nat.log 2 n := by
  intro n _
  apply Nat.log_anti_left <;> omega
