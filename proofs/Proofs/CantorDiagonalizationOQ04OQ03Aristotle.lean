/-
  Aristotle targets for CantorDiagonalizationOQ04OQ03
  Routine supporting lemmas for automated proof search.
  See CantorDiagonalizationOQ04OQ03.lean for the Lawvere-Kleene formalization.

  Criteria for inclusion:
  - Routine derivation from ω-continuity: monotonicity via a step chain
  - The chain construction a, b, b, b, ... connects ω-continuity to monotonicity
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (1):
  - omega_continuous_monotone_ari: ω-continuous functions are monotone

  Strategy: Given a ≤ b, build the ascending chain c(0) = a, c(n+1) = b.
  Then ⨆ c = b (chain is eventually b), so by ω-continuity:
    f b = f(⨆ c) = ⨆(f ∘ c) ≥ f(c 0) = f a.

  NOT included:
  - Lawvere fixed-point theorem (already proved in main file)
  - Kleene fixed-point theorem (already proved in main file)
  - Least fixed-point property (already proved in main file)
-/
import Mathlib
import Proofs.CantorDiagonalizationOQ04OQ03

namespace CantorDiagonalizationOQ04OQ03Aristotle

open CantorDiagonalizationOQ04OQ03

/-
## ω-Continuity Implies Monotonicity

Given a ≤ b, we need to show f a ≤ f b. The key is to use the step chain:
  c n = if n = 0 then a else b

This chain is ascending (a ≤ b, then constant) with supremum b.
By ω-continuity: f(⨆ n, c n) = ⨆ n, f(c n)
So: f b = ⨆ n, f(c n) ≥ f(c 0) = f a.
-/

/-- ω-continuous functions on complete lattices are monotone.
    Proof: use the step chain c(0)=a, c(n+1)=b with sup=b and apply ω-continuity. -/
theorem omega_continuous_monotone_ari {α : Type*} [CompleteLattice α] {f : α → α}
    (hf : OmegaContinuous f) : Monotone f := by
  intro a b hab
  -- Build the step chain c(0) = a, c(n+1) = b
  have hc_asc : ∀ n : ℕ, (fun n => if n = 0 then a else b) n ≤
                           (fun n => if n = 0 then a else b) (n + 1) := fun n => by
    rcases n with _ | n <;> simp [hab]
  -- The supremum of this chain is b
  have hc_sup : ⨆ n : ℕ, (if n = 0 then a else b) = b := by
    apply le_antisymm
    · exact iSup_le fun n => by rcases n with _ | n <;> simp [hab]
    · exact le_iSup_of_le 1 (by simp)
  -- Apply ω-continuity: f(⨆ c) = ⨆ f(c)
  have h := hf _ hc_asc
  rw [hc_sup] at h
  -- f a = f(c 0) ≤ ⨆ f(c) = f b
  calc f a = f (if (0 : ℕ) = 0 then a else b) := by simp
       _ ≤ ⨆ n, f (if n = 0 then a else b) := le_iSup _ 0
       _ = f b := h.symm

end CantorDiagonalizationOQ04OQ03Aristotle
