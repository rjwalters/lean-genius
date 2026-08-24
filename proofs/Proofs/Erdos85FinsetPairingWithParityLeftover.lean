import Proofs.Erdos85EvenFinsetPairing

/-!
# Pairing a finite source with its parity leftover

Every finite source decomposes into paired two-ended columns and at most one
leftover.  The leftover is present exactly when the source cardinality is
odd.  Applied on each pole line, this is the combinatorial compression in
`(73rnz_cjic)`.
-/

namespace Erdos85

/-- An odd finite set has an element whose deletion is even and hence
pairable. -/
theorem exists_leftover_and_pairing_of_odd_card
    {O : Type*} [DecidableEq O] (S : Finset O) (hodd : Odd S.card) :
    ∃ x ∈ S, ∃ mate : O → O,
      (∀ o ∈ S.erase x, mate o ∈ S.erase x) ∧
      (∀ o ∈ S.erase x, mate (mate o) = o) ∧
      (∀ o ∈ S.erase x, mate o ≠ o) := by
  have hpos : 0 < S.card := by
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hcard := Finset.card_erase_add_one hx
  have heven : Even (S.erase x).card := by
    rcases hodd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  obtain ⟨mate, hclosed, hinvol, hfree⟩ :=
    exists_closed_fixedPointFree_involution_of_even_card (S.erase x) heven
  exact ⟨x, hx, mate, hclosed, hinvol, hfree⟩

/-- **Parity-leftover pairing.**  An arbitrary finite source contains a
pairable subfinset whose complement has size at most one; that complement
has size one exactly when the original source is odd. -/
theorem exists_pairable_subfinset_with_parity_leftover
    {O : Type*} [DecidableEq O] (S : Finset O) :
    ∃ R : Finset O, ∃ mate : O → O,
      R ⊆ S ∧
      (S \ R).card ≤ 1 ∧
      ((S \ R).card = 1 ↔ Odd S.card) ∧
      (∀ o ∈ R, mate o ∈ R) ∧
      (∀ o ∈ R, mate (mate o) = o) ∧
      (∀ o ∈ R, mate o ≠ o) := by
  rcases Nat.even_or_odd S.card with heven | hodd
  · obtain ⟨mate, hclosed, hinvol, hfree⟩ :=
      exists_closed_fixedPointFree_involution_of_even_card S heven
    refine ⟨S, mate, Finset.Subset.rfl, ?_, ?_, hclosed, hinvol, hfree⟩
    · simp
    · simp [Nat.not_odd_iff_even.mpr heven]
  · obtain ⟨x, hx, mate, hclosed, hinvol, hfree⟩ :=
      exists_leftover_and_pairing_of_odd_card S hodd
    refine ⟨S.erase x, mate, Finset.erase_subset x S, ?_, ?_,
      hclosed, hinvol, hfree⟩
    · simpa [Finset.sdiff_erase, hx]
    · simp [Finset.sdiff_erase, hx, hodd]

end Erdos85

#print axioms Erdos85.exists_leftover_and_pairing_of_odd_card
#print axioms Erdos85.exists_pairable_subfinset_with_parity_leftover
