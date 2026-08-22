import Mathlib

/-! # Reciprocity pruning for finite neighborhood-pattern systems

This is the abstract monotone engine behind the q=9 marked-pair row
obstruction.  A candidate at `p` is a finite set of proposed neighbors.  One
pruning round removes a candidate containing `q` unless `q` still has some
candidate containing `p`.  Any genuinely reciprocal global choice survives
every round, so an empty pruned fiber certifies impossibility.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Delete every local pattern containing an arc unsupported in the reverse
direction by the current pattern families. -/
def reciprocalPatternPrune {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) : α → Finset (Finset α) :=
  fun p => (F p).filter fun S => ∀ q ∈ S, ∃ T ∈ F q, p ∈ T

/-- A reciprocal choice from `F` remains available after one pruning round. -/
theorem reciprocal_choice_mem_prune
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) (C : α → Finset α)
    (hmem : ∀ p, C p ∈ F p)
    (hrecip : ∀ p q, q ∈ C p ↔ p ∈ C q) :
    ∀ p, C p ∈ reciprocalPatternPrune F p := by
  intro p
  rw [reciprocalPatternPrune, Finset.mem_filter]
  refine ⟨hmem p, ?_⟩
  intro q hq
  exact ⟨C q, hmem q, (hrecip p q).mp hq⟩

/-- A reciprocal global choice survives every finite number of pruning
rounds. -/
theorem reciprocal_choice_mem_iterate_prune
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α)) (C : α → Finset α)
    (hmem : ∀ p, C p ∈ F p)
    (hrecip : ∀ p q, q ∈ C p ↔ p ∈ C q) :
    ∀ n p, C p ∈ (reciprocalPatternPrune^[n]) F p := by
  intro n
  induction n with
  | zero =>
      intro p
      simpa using hmem p
  | succ n ih =>
      intro p
      rw [Function.iterate_succ_apply']
      exact reciprocal_choice_mem_prune
        ((reciprocalPatternPrune^[n]) F) C ih hrecip p

/-- Emptying one pattern fiber after finitely many rounds rules out every
reciprocal global selection. -/
theorem no_reciprocal_choice_of_iterate_prune_eq_empty
    {α : Type*} [DecidableEq α]
    (F : α → Finset (Finset α))
    (n : ℕ) (p : α)
    (hempty : (reciprocalPatternPrune^[n]) F p = ∅) :
    ¬ ∃ C : α → Finset α,
      (∀ q, C q ∈ F q) ∧ (∀ q r, r ∈ C q ↔ q ∈ C r) := by
  rintro ⟨C, hmem, hrecip⟩
  have hp := reciprocal_choice_mem_iterate_prune F C hmem hrecip n p
  rw [hempty] at hp
  simpa using hp

end

end Erdos85

#print axioms Erdos85.no_reciprocal_choice_of_iterate_prune_eq_empty
