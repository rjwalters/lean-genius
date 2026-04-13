/-
  Aristotle targets for Erdős Problem #817
  Routine supporting lemmas for automated proof search.
  See Erdos817Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (g_3(n) ≫ 3^n)
  - NOT the Erdős-Sárközy partial result (deep sieve argument)
  - Routine combinatorics: subset sum cardinalities, AP-free small sets, Icc bounds
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections
-/
import Mathlib

namespace Erdos817Aristotle

open Finset Filter Nat

/-
  ## Section 1: Arithmetic Progression Freeness

  A set with fewer than 3 elements cannot contain a 3-term AP.
  These support g3_one and related small-case bounds.
-/

-- Aristotle target: set of cardinality < 3 is 3-AP-free
-- If |S| < 3, there are no 3 distinct elements, so no 3-AP exists
theorem apFree_of_card_lt_three (S : Finset ℕ) (hS : S.card < 3) :
    ∀ a d, d > 0 → ∃ i < 3, a + i * d ∉ (S : Set ℕ) := by sorry

-- Aristotle target: {0, 1} contains no 3-term AP
-- Only 2 elements, need 3 for an AP
theorem apFree_zero_one : ∀ a d, d > 0 → ∃ i < 3, a + i * d ∉ ({0, 1} : Set ℕ) := by sorry

-- Aristotle target: no 3-AP in a 2-element set of naturals
theorem two_element_nat_set_apFree (x y : ℕ) (hxy : x ≠ y) :
    ∀ a d, d > 0 → ∃ i < 3, a + i * d ∉ ({x, y} : Set ℕ) := by sorry

/-
  ## Section 2: Subset Sum Properties

  The subset sum set of a singleton {a} is {0, a}.
  Supporting g3_one: g_3(1) = 1 since {1} has AP-free subset sums.
-/

-- Local definition matching the main file
def subsetSumsLocal (A : Finset ℕ) : Finset ℕ :=
  A.powerset.image (fun B => B.sum id)

-- Aristotle target: subsetSums of singleton is {0, a}
theorem subsetSums_singleton (a : ℕ) :
    subsetSumsLocal {a} = {0, a} := by sorry

-- Aristotle target: subsetSums of singleton has cardinality 2 (when a ≠ 0)
theorem card_subsetSums_singleton (a : ℕ) (ha : a ≠ 0) :
    (subsetSumsLocal {a}).card = 2 := by sorry

-- Aristotle target: subsetSums of singleton has cardinality ≤ 2
theorem card_subsetSums_singleton_le (a : ℕ) :
    (subsetSumsLocal {a}).card ≤ 2 := by sorry

/-
  ## Section 3: Icc Cardinality Bounds

  Any A ⊆ Icc 1 N with |A| = n requires N ≥ n.
  This supports g_ge_n: g_k(n) ≥ n.
-/

-- Aristotle target: |Icc 1 N| = N
theorem card_Icc_one (N : ℕ) : (Finset.Icc 1 N).card = N := by sorry

-- Aristotle target: if A ⊆ Icc 1 N then |A| ≤ N
theorem subset_Icc_card_le (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    A.card ≤ N := by sorry

-- Aristotle target: N ≥ n when some A ⊆ Icc 1 N has |A| = n
theorem Icc_contains_n_elements (A : Finset ℕ) (n N : ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hn : A.card = n) :
    N ≥ n := by sorry

/-
  ## Section 4: Powers of 3 are in Icc 1 (3^n)

  Supporting g3_le_exp: g_3(n) ≤ 3^n.
  The set {3^0, 3^1, ..., 3^(n-1)} ⊆ {1,...,3^n-1} ⊆ {1,...,3^n}.
-/

-- Aristotle target: 3^i ≥ 1 for all i (so powers of 3 are in Icc 1 ...)
theorem three_pow_pos (i : ℕ) : 0 < 3^i := by sorry

-- Aristotle target: 3^i ≤ 3^n for i < n
theorem three_pow_le_pow (i n : ℕ) (hi : i < n) : 3^i ≤ 3^n := by sorry

-- Aristotle target: 3^i ∈ Finset.Icc 1 (3^n) for i < n
theorem three_pow_mem_Icc (i n : ℕ) (hi : i < n) :
    3^i ∈ Finset.Icc 1 (3^n) := by sorry

end Erdos817Aristotle
