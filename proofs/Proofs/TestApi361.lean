-- Test API for Erdos 361 proof
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Finset

def IsSubsetSum' (A : Finset ℕ) (n : ℕ) : Prop :=
    ∃ B : Finset ℕ, B ⊆ A ∧ B.sum id = n

theorem test_empty (n : ℕ) (hn : 0 < n) : ¬IsSubsetSum' ∅ n := by
  intro ⟨B, hB, hsum⟩
  have : B = ∅ := eq_empty_of_forall_not_mem (fun x hx =>
    absurd (hB hx) (not_mem_empty x))
  subst this
  simp at hsum
  omega

theorem test_subset {A B : Finset ℕ} {n : ℕ}
    (h : A ⊆ B) (hB : ¬IsSubsetSum' B n) : ¬IsSubsetSum' A n := by
  intro ⟨C, hCA, hsum⟩
  exact hB ⟨C, Finset.Subset.trans hCA h, hsum⟩

theorem test_singleton (n : ℕ) (hn : 2 ≤ n) : ¬IsSubsetSum' {1} n := by
  intro ⟨B, hB, hsum⟩
  rw [Finset.subset_singleton_iff] at hB
  rcases hB with rfl | rfl
  · simp at hsum; omega
  · simp at hsum; omega
