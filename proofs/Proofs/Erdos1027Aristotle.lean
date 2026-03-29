/-
  Aristotle targets for Erdős Problem #1027
  Routine supporting lemmas for automated proof search.
  See Erdos1027Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

noncomputable section

namespace Erdos1027Aristotle

open Finset Fintype

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The number of functions α → Bool that take constant value b on A ⊆ α
    is exactly 2^(|α| - |A|). Elements in A are fixed, elements outside
    are free to take either value.

    This is a standard counting result: the set {f : α → Bool | ∀ x ∈ A, f x = b}
    is in bijection with functions (α \ A) → Bool via restriction. -/
theorem card_constOn (A : Finset α) (b : Bool) :
    (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = b)).card
    = 2 ^ (Fintype.card α - A.card) := by
  sorry

end Erdos1027Aristotle

end
