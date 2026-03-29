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

/-
PROBLEM
The number of functions α → Bool that take constant value b on A ⊆ α
    is exactly 2^(|α| - |A|). Elements in A are fixed, elements outside
    are free to take either value.

    This is a standard counting result: the set {f : α → Bool | ∀ x ∈ A, f x = b}
    is in bijection with functions (α \ A) → Bool via restriction.

PROVIDED SOLUTION
We construct an explicit bijection between {f : α → Bool | ∀ x ∈ A, f x = b} and functions (Aᶜ → Bool). Given such an f, restrict it to the complement of A in univ. Conversely, given g : (↑(univ \ A) → Bool), define f by cases. This is a bijection, so the cardinality equals 2^|univ \ A| = 2^(card α - card A).

Alternative approach: induction on A. Base case A = ∅: the filter is all of univ, card = 2^(card α) = 2^(card α - 0). Inductive step: partition by the value at a new element a, use Finset.filter_congr and card manipulations.
-/
theorem card_constOn (A : Finset α) (b : Bool) :
    (Finset.univ.filter (fun f : α → Bool => ∀ x ∈ A, f x = b)).card
    = 2 ^ (Fintype.card α - A.card) := by
  -- We construct an explicit bijection between {f : α → Bool | ∀ x ∈ A, f x = b} and functions (Aᶜ → Bool). Given such an f, restrict it to the complement of A in univ.
  have h_bij : {f : α → Bool | ∀ x ∈ A, f x = b} ≃ (↥(Finset.univ \ A) → Bool) := by
    refine' Equiv.ofBijective ( fun f => fun x => f.val x ) ⟨ fun f g h => _, fun g => _ ⟩;
    · ext x; by_cases hx : x ∈ A <;> simp_all +decide [ funext_iff ] ;
      convert f.2 x hx |> Eq.trans <| g.2 x hx |> Eq.symm;
    · refine' ⟨ ⟨ fun x => if hx : x ∈ univ \ A then g ⟨ x, hx ⟩ else b, _ ⟩, _ ⟩ <;> aesop;
  have := Fintype.card_congr h_bij; simp_all +decide [ Fintype.card_pi ] ;
  rw [ ← this, Fintype.card_subtype ]

end Erdos1027Aristotle

end