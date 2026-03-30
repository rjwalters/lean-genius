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
  induction n with
  | zero =>
    intro S T hS hT _
    rw [Finset.range_zero] at hS hT
    rw [Finset.subset_empty.mp hS, Finset.subset_empty.mp hT]
  | succ n ih =>
    intro S T hS hT heq
    -- Helper: if n ∉ X and X ⊆ range (n+1), then X ⊆ range n
    have restrict : ∀ X : Finset ℕ, X ⊆ Finset.range (n + 1) → n ∉ X →
        X ⊆ Finset.range n := by
      intro X hX hn x hx
      have := hX hx
      have : x ≠ n := fun h => hn (h ▸ hx)
      simp [Finset.mem_range] at *; omega
    by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T
    · -- Both contain n: erase n from both, apply IH
      have hS' : S.erase n ⊆ Finset.range n := by
        intro x hx
        have hxne := (Finset.mem_erase.mp hx).1
        have := hS (Finset.mem_of_mem_erase hx)
        simp [Finset.mem_range] at this ⊢; omega
      have hT' : T.erase n ⊆ Finset.range n := by
        intro x hx
        have hxne := (Finset.mem_erase.mp hx).1
        have := hT (Finset.mem_of_mem_erase hx)
        simp [Finset.mem_range] at this ⊢; omega
      have hSeq : S.sum (2 ^ ·) = 2 ^ n + (S.erase n).sum (2 ^ ·) := by
        rw [← Finset.add_sum_erase _ _ hnS]
      have hTeq : T.sum (2 ^ ·) = 2 ^ n + (T.erase n).sum (2 ^ ·) := by
        rw [← Finset.add_sum_erase _ _ hnT]
      have heq' : (S.erase n).sum (2 ^ ·) = (T.erase n).sum (2 ^ ·) := by omega
      have := ih _ _ hS' hT' heq'
      rw [← Finset.insert_erase hnS, ← Finset.insert_erase hnT, this]
    · -- n ∈ S, n ∉ T: sum(S) ≥ 2^n but sum(T) ≤ 2^n - 1, contradiction
      exfalso
      have hT' := restrict T hT hnT
      have hSge : S.sum (2 ^ ·) ≥ 2 ^ n := by
        calc S.sum (2 ^ ·)
            ≥ ({n} : Finset ℕ).sum (2 ^ ·) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnS) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := Finset.sum_singleton
      have hTle := subset_pow_two_sum_le' hT'
      omega
    · -- n ∉ S, n ∈ T: symmetric case
      exfalso
      have hS' := restrict S hS hnS
      have hTge : T.sum (2 ^ ·) ≥ 2 ^ n := by
        calc T.sum (2 ^ ·)
            ≥ ({n} : Finset ℕ).sum (2 ^ ·) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnT) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := Finset.sum_singleton
      have hSle := subset_pow_two_sum_le' hS'
      omega
    · -- Neither contains n: both ⊆ range n, apply IH directly
      exact ih _ _ (restrict S hS hnS) (restrict T hT hnT) heq

end ConwayGuy
