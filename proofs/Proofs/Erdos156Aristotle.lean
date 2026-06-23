/-
  Aristotle targets for Erdos156 (Maximal Sidon Sets of Size O(N^{1/3}))
  Routine supporting lemmas for automated proof search.
  See Erdos156Problem.lean for the main formalization.

  These lemmas provide building blocks for maximal Sidon set analysis:
  - IsSidonSet basic properties
  - sumset size bound (n*(n+1)/2 for Sidon set of size n)
  - diffShadow and midShadow cardinality helpers
  - Set.ncard counting lemmas
  - Cube lower bound arithmetic
-/
import Mathlib

namespace Erdos156.Aristotle

open Set

/-
  ## Section 1: Sidon Set Properties
-/

def IsSidonSet' (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → a ≤ b → c ≤ d → (a = c ∧ b = d)

/-- Sidon set: all pairwise sums distinct means |A+A| = C(n,2) + n = n*(n+1)/2 -/
lemma sidon_sumset_ncard (A : Set ℕ) (hS : IsSidonSet' A) (hfin : A.Finite) :
    (A + A).ncard ≤ A.ncard * (A.ncard + 1) / 2 + A.ncard := by
  sorry

/-- In a Sidon set, a + b = c + d with a ≤ b, c ≤ d implies {a,b} = {c,d} -/
lemma sidon_unique_pair (A : Set ℕ) (hS : IsSidonSet' A)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≤ b) (hcd : c ≤ d) (heq : a + b = c + d) : a = c ∧ b = d := by
  sorry

/-
  ## Section 2: Shadow Set Size Bounds
-/

/-- Union of shadows has ncard ≤ sum of ncards -/
lemma ncard_union_le (S T : Set ℕ) (hS : S.Finite) (hT : T.Finite) :
    (S ∪ T).ncard ≤ S.ncard + T.ncard := by
  sorry

/-- ncard of union of 3 sets ≤ sum of ncards -/
lemma ncard_union3_le (S T U : Set ℕ) (hS : S.Finite) (hT : T.Finite) (hU : U.Finite) :
    (S ∪ T ∪ U).ncard ≤ S.ncard + T.ncard + U.ncard := by
  sorry

/-- If A ⊆ B then A.ncard ≤ B.ncard for finite B -/
lemma ncard_le_of_subset (A B : Set ℕ) (hAB : A ⊆ B) (hB : B.Finite) :
    A.ncard ≤ B.ncard := by
  sorry

/-- The diffShadow fiber size: {σ - a | σ ∈ sumset, σ > a} has size ≤ |sumset| -/
lemma fiber_ncard_le_sumset (A : Set ℕ) (a : ℕ) (ha : a ∈ A) (hfin : A.Finite) :
    { x | ∃ σ ∈ A + A, σ > a ∧ σ - a = x }.ncard ≤ (A + A).ncard := by
  sorry

/-
  ## Section 3: Cube Lower Bound Arithmetic
-/

/-- n + n*(n*(n+1)/2) + n*(n+1)/2 ≤ n + n^3/2 + n^2/2 for any n -/
lemma cube_bound_ineq (n : ℕ) :
    n + n * (n * (n + 1) / 2) + n * (n + 1) / 2 ≤ n + n^3 / 2 + n^2 / 2 := by
  sorry

/-- If N ≤ n + n*(n*(n+1)/2) + n*(n+1)/2 then n ≥ N^{1/3}/C for some C -/
lemma cube_root_lower_bound (N n : ℕ) (hN : N ≥ 1)
    (h : N ≤ n + n * (n * (n + 1) / 2) + n * (n + 1) / 2) :
    (n : ℝ) ≥ (N : ℝ) ^ (1/3 : ℝ) / 2 := by
  sorry

/-- n*(n+1)/2 ≤ n^2 for n ≥ 1 -/
lemma triangular_le_sq (n : ℕ) : n * (n + 1) / 2 ≤ n ^ 2 := by
  sorry

/-- n*(n*(n+1)/2) ≤ n^3/2 -/
lemma cubic_bound (n : ℕ) : n * (n * (n + 1) / 2) ≤ n ^ 3 / 2 + n ^ 2 / 2 := by
  sorry

/-
  ## Section 4: Set.ncard Finset Helpers
-/

/-- Interval {1, ..., N} has ncard = N -/
lemma Icc_ncard (N : ℕ) : (Set.Icc 1 N).ncard = N := by
  sorry

/-- A finite set A and its diffShadow are both finite -/
lemma diffShadow_finite (A : Set ℕ) (hfin : A.Finite) :
    (A - A : Set ℤ).Finite := by
  sorry

end Erdos156.Aristotle
