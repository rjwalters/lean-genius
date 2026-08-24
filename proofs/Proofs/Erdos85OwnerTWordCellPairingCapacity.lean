import Proofs.Erdos85EvenFinsetInvolutionPairing

/-!
# Owner/T-word cell pairing capacity

The fine capacity question in `(73rnz_cm)` asks for a pairing that does not
forget the owner/T-word cell of an occurrence.  Once every labeled cell has
even size, the existing fiberwise pairing theorem assembles into one global
fixed-point-free involution preserving that label.  The second theorem
applies this after adjoining the pole-owner leftovers as a disjoint summand.
-/

namespace Erdos85

noncomputable section

/-- **Labeled capacity engine.**  Cellwise evenness is sufficient for one
global free involution whose every pair stays in a single label cell. -/
theorem exists_labelPreserving_freeInvolution_of_even_fibers
    {O L : Type*} [Fintype O] [Fintype L]
    [DecidableEq O] [DecidableEq L]
    (label : O → L)
    (heven : ∀ l,
      Even ((Finset.univ.filter fun o => label o = l).card)) :
    ∃ mate : O → O,
      (∀ o, label (mate o) = label o) ∧
      Function.Involutive mate ∧
      (∀ o, mate o ≠ o) := by
  let eligible : L → O → Prop := fun l o => label o = l
  letI : DecidableRel eligible := fun _ _ => inferInstance
  obtain ⟨fiberMate, hclosed, hinvol, hfree, _houtside⟩ :=
    exists_witnessMate_of_even_fibers eligible heven
  let mate : O → O := fun o => fiberMate (label o) o
  have hlabel : ∀ o, label (mate o) = label o := by
    intro o
    exact hclosed (label o) o rfl
  refine ⟨mate, hlabel, ?_, ?_⟩
  · intro o
    change fiberMate (label (mate o)) (mate o) = o
    rw [hlabel o]
    exact hinvol (label o) o rfl
  · intro o
    exact hfree (label o) o rfl

/-- Adjoin a separate family of owner-leftover atoms to the geometric
occurrences.  If every combined owner/T-word cell is even, all geometric
and leftover atoms admit one label-preserving pairing. -/
theorem exists_augmented_labelPreserving_freeInvolution_of_even_fibers
    {O P L : Type*} [Fintype O] [Fintype P] [Fintype L]
    [DecidableEq O] [DecidableEq P] [DecidableEq L]
    (occurrenceLabel : O → L) (ownerLabel : P → L)
    (heven : ∀ l,
      Even ((Finset.univ.filter fun x : Sum O P =>
        Sum.elim occurrenceLabel ownerLabel x = l).card)) :
    ∃ mate : Sum O P → Sum O P,
      (∀ x, Sum.elim occurrenceLabel ownerLabel (mate x) =
        Sum.elim occurrenceLabel ownerLabel x) ∧
      Function.Involutive mate ∧
      (∀ x, mate x ≠ x) :=
  exists_labelPreserving_freeInvolution_of_even_fibers
    (Sum.elim occurrenceLabel ownerLabel) heven

end

end Erdos85

#print axioms Erdos85.exists_labelPreserving_freeInvolution_of_even_fibers
#print axioms Erdos85.exists_augmented_labelPreserving_freeInvolution_of_even_fibers
