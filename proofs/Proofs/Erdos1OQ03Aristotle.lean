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
import Mathlib

open Finset

namespace ConwayGuy

/-- ∑_{i=0}^{n-1} 2^i + 1 = 2^n -/
theorem geom_sum_two' (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    omega

/-- Any subset of {0,...,n-1} has power-of-2 sum ≤ 2^n - 1. -/
theorem subset_pow_two_sum_le' {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range n) :
    S.sum (2 ^ ·) ≤ 2 ^ n - 1 := by
  have h1 : S.sum (2 ^ ·) ≤ (Finset.range n).sum (2 ^ ·) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have h2 := geom_sum_two' n
  omega

/-
PROBLEM
Binary representation uniqueness: distinct subsets of {0,...,n-1}
    have distinct power-of-2 sums. By induction on n.

PROVIDED SOLUTION
Induction on n. Base case n=0: both S and T are subsets of range 0 = ∅, so S = T = ∅. Inductive step: assume the result for n, prove for n+1. For S ⊆ range (n+1), consider whether n ∈ S and n ∈ T. Case 1: n ∈ S and n ∈ T. Then S.sum (2^·) = (S.erase n).sum (2^·) + 2^n and similarly for T. From the sum equality, (S.erase n).sum (2^·) = (T.erase n).sum (2^·). Both S.erase n and T.erase n are subsets of range n (since they don't contain n and are subsets of range (n+1)). By IH, S.erase n = T.erase n, so S = T. Case 2: n ∉ S and n ∉ T. Then S, T ⊆ range n (since they're subsets of range (n+1) not containing n). Apply IH directly. Case 3: n ∈ S but n ∉ T (or vice versa). Then S.sum (2^·) ≥ 2^n but T.sum (2^·) ≤ 2^n - 1 by subset_pow_two_sum_le', contradiction. Use Finset.subset_range_succ_iff or the fact that if S ⊆ range (n+1) and n ∉ S then S ⊆ range n.
-/
theorem pow_two_sum_injective (n : ℕ) :
    ∀ S T : Finset ℕ, S ⊆ Finset.range n → T ⊆ Finset.range n →
    S.sum (2 ^ ·) = T.sum (2 ^ ·) → S = T := by
  intro S T hS hT h_eq; induction' n with n ih generalizing S T; simp_all +decide [ Finset.subset_iff, Finset.sum_range_succ ] ;
  · rw [ Finset.eq_empty_of_forall_notMem hS, Finset.eq_empty_of_forall_notMem hT ];
  · by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T;
    · -- If both $n \in S$ and $n \in T$, then we can remove $n$ from both sets and apply the induction hypothesis.
      have h_ind : ∑ x ∈ S.erase n, 2 ^ x = ∑ x ∈ T.erase n, 2 ^ x := by
        simp_all +decide [ ← Finset.sum_erase_add _ _ hnS, ← Finset.sum_erase_add _ _ hnT ];
      specialize ih ( S.erase n ) ( T.erase n ) ; simp_all +decide [ Finset.subset_iff ] ;
      simp_all +decide [ Finset.ext_iff ];
      grind +ring;
    · -- Since $n \notin T$, we have $\sum_{x \in T} 2^x \leq \sum_{x \in \{0, 1, ..., n-1\}} 2^x = 2^n - 1$.
      have hT_le : ∑ x ∈ T, 2 ^ x ≤ ∑ x ∈ Finset.range n, 2 ^ x := by
        exact Finset.sum_le_sum_of_subset ( fun x hx => Finset.mem_range.mpr ( Nat.lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ( hT hx ) ) fun h => hnT <| h ▸ hx ) );
      exact absurd hT_le ( by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ), geom_sum_two' n, Finset.single_le_sum ( fun x _ => Nat.zero_le ( 2 ^ x ) ) hnS ] );
    · -- Since $n \in T$ and $n \notin S$, we have $\sum_{x \in S} 2^x \leq 2^n - 1$ and $\sum_{x \in T} 2^x \geq 2^n$.
      have h_sum_S : ∑ x ∈ S, 2 ^ x ≤ 2 ^ n - 1 := by
        exact subset_pow_two_sum_le' <| Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Nat.lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp <| hS hx ) fun con => hnS <| con ▸ hx;
      have h_sum_T : ∑ x ∈ T, 2 ^ x ≥ 2 ^ n := by
        exact Finset.single_le_sum ( fun x _ => Nat.zero_le ( 2 ^ x ) ) hnT;
      exact absurd h_sum_T ( by linarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ) ] );
    · exact ih S T ( fun x hx => Finset.mem_range.mpr ( Nat.lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ( hS hx ) ) ( by aesop ) ) ) ( fun x hx => Finset.mem_range.mpr ( Nat.lt_of_le_of_ne ( Finset.mem_range_succ_iff.mp ( hT hx ) ) ( by aesop ) ) ) h_eq

end ConwayGuy