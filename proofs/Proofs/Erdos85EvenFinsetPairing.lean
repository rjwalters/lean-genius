import Proofs.Erdos85FinsetInvolutionParity
import Proofs.Erdos85TwoPoleOwnerRoutingAlternative

/-!
# Pairing an even finite occurrence set

Componentwise Eulerian cut parity gives an even set of cut occurrences.
To route owners, one also needs an actual pairing of those occurrences.
This file supplies the converse to the fixed-point-free involution parity
lemma: every even finset admits such an involution.
-/

namespace Erdos85

/-- Every even finite set admits a closed fixed-point-free involution.
Outside the set the resulting function is intentionally unconstrained. -/
theorem exists_closed_fixedPointFree_involution_of_even_card
    {O : Type*} [DecidableEq O] (S : Finset O) (heven : Even S.card) :
    ∃ mate : O → O,
      (∀ o ∈ S, mate o ∈ S) ∧
      (∀ o ∈ S, mate (mate o) = o) ∧
      (∀ o ∈ S, mate o ≠ o) := by
  induction S using Finset.strongInduction with
  | H S ih =>
      classical
      by_cases hS : S = ∅
      · refine ⟨id, ?_, ?_, ?_⟩ <;> simp [hS]
      · obtain ⟨x, hxS⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        have hcardTwo : 2 ≤ S.card := by
          rcases heven with ⟨k, hk⟩
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hxS⟩
          omega
        have hErase : (S.erase x).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          have hcardErase : (S.erase x).card = 0 := by simp [hempty]
          have hcard := Finset.card_erase_add_one hxS
          omega
        obtain ⟨y, hyErase⟩ := hErase
        have hyx : y ≠ x := (Finset.mem_erase.mp hyErase).1
        have hyS : y ∈ S := (Finset.mem_erase.mp hyErase).2
        let R := (S.erase x).erase y
        have hRsub : R ⊂ S := by
          rw [Finset.ssubset_iff_subset_ne]
          constructor
          · exact (Finset.erase_subset y (S.erase x)).trans
              (Finset.erase_subset x S)
          · intro hEq
            have hxR : x ∈ R := hEq ▸ hxS
            exact (Finset.mem_erase.mp
              (Finset.mem_erase.mp hxR).2).1 rfl
        have hcardX := Finset.card_erase_add_one hxS
        have hcardY := Finset.card_erase_add_one hyErase
        change R.card + 1 = (S.erase x).card at hcardY
        have hReven : Even R.card := by
          rcases heven with ⟨k, hk⟩
          use k - 1
          omega
        obtain ⟨mateR, hRclosed, hRinvol, hRfree⟩ := ih R hRsub hReven
        let mate : O → O := fun o => if o = x then y else if o = y then x else mateR o
        refine ⟨mate, ?_, ?_, ?_⟩
        · intro o hoS
          by_cases hox : o = x
          · simp [mate, hox, hyS]
          by_cases hoy : o = y
          · subst o
            simp [mate, hyx, hxS]
          have hoR : o ∈ R := by
            exact Finset.mem_erase.mpr ⟨hoy,
              Finset.mem_erase.mpr ⟨hox, hoS⟩⟩
          have hmR := hRclosed o hoR
          have hmS : mateR o ∈ S :=
            (Finset.erase_subset y (S.erase x) |>.trans
              (Finset.erase_subset x S)) hmR
          simp [mate, hox, hoy, hmS]
        · intro o hoS
          by_cases hox : o = x
          · subst o
            simp [mate, hyx]
          by_cases hoy : o = y
          · subst o
            simp [mate, hyx]
          have hoR : o ∈ R := Finset.mem_erase.mpr ⟨hoy,
            Finset.mem_erase.mpr ⟨hox, hoS⟩⟩
          have hmR := hRclosed o hoR
          have hmx : mateR o ≠ x := by
            exact (Finset.mem_erase.mp
              (Finset.mem_erase.mp hmR).2).1
          have hmy : mateR o ≠ y := (Finset.mem_erase.mp hmR).1
          simp [mate, hox, hoy, hmx, hmy, hRinvol o hoR]
        · intro o hoS
          by_cases hox : o = x
          · subst o
            simp [mate, hyx]
          by_cases hoy : o = y
          · subst o
            simp [mate, hyx, hyx.symm]
          have hoR : o ∈ R := Finset.mem_erase.mpr ⟨hoy,
            Finset.mem_erase.mpr ⟨hox, hoS⟩⟩
          simpa [mate, hox, hoy] using hRfree o hoR

/-- The parity criterion is exact: a finite set can be paired by a closed
fixed-point-free involution if and only if its cardinality is even. -/
theorem even_card_iff_exists_closed_fixedPointFree_involution
    {O : Type*} [DecidableEq O] (S : Finset O) :
    Even S.card ↔
      ∃ mate : O → O,
        (∀ o ∈ S, mate o ∈ S) ∧
        (∀ o ∈ S, mate (mate o) = o) ∧
        (∀ o ∈ S, mate o ≠ o) := by
  constructor
  · exact exists_closed_fixedPointFree_involution_of_even_card S
  · rintro ⟨mate, hclosed, hinvol, hfree⟩
    exact even_card_of_closed_fixedPointFree_involution
      mate S hclosed hinvol hfree

/-- Even cut parity plus two distinct marked poles produces an actual
owner-retaining routing alternative.  This is the direct abstract interface
from componentwise Eulerian cut parity to the two-pole routing consumer. -/
theorem exists_pairing_with_twoPoleOwnerRoutingAlternative
    {O : Type*} [DecidableEq O] (S : Finset O) (pole : Bool → O)
    (heven : Even S.card) (hpole : ∀ owner, pole owner ∈ S)
    (hpoles : Function.Injective pole) :
    ∃ mate : O → O,
      (∀ o ∈ S, mate o ∈ S) ∧
      (∀ o ∈ S, mate (mate o) = o) ∧
      (∀ o ∈ S, mate o ≠ o) ∧
      (mate (pole false) = pole true ∨
        (Function.Injective (twoPoleOwnerExit mate pole) ∧
          ∀ owner, twoPoleOwnerExit mate pole owner ∈
            twoPoleOrdinaryOccurrences S (pole false) (pole true))) := by
  obtain ⟨mate, hclosed, hinvol, hfree⟩ :=
    exists_closed_fixedPointFree_involution_of_even_card S heven
  refine ⟨mate, hclosed, hinvol, hfree, ?_⟩
  exact twoPoleOwnerExit_crossOwner_or_injective_ordinary
    mate S pole hpole hpoles hclosed hinvol hfree

end Erdos85

#print axioms Erdos85.exists_closed_fixedPointFree_involution_of_even_card
#print axioms Erdos85.even_card_iff_exists_closed_fixedPointFree_involution
#print axioms Erdos85.exists_pairing_with_twoPoleOwnerRoutingAlternative
