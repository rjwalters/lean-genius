import Proofs.Erdos85PrescribedPairInvolution

/-!
# Owner-pair selection in an even broken fiber

The one-special-leaf Baer state needs a broken nonleaf exit.  An even broken
fiber containing exactly one leaf cannot consist only of that leaf, so such
an endpoint exists and can be forced as its mate.
-/

namespace Erdos85

noncomputable section

/-- An even finite fiber with exactly one marked leaf contains a distinct
unmarked endpoint. -/
theorem exists_nonleaf_of_even_of_unique_leaf
    {V : Type*} [DecidableEq V] (S : Finset V) (leaf : V → Prop)
    (a : V) (heven : Even S.card) (haS : a ∈ S) (_haLeaf : leaf a)
    (hunique : ∀ x ∈ S, leaf x → x = a) :
    ∃ b ∈ S, b ≠ a ∧ ¬ leaf b := by
  obtain ⟨k, hk⟩ := heven
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, haS⟩
  have htwo : 1 < S.card := by omega
  obtain ⟨b, hbS, hba⟩ := Finset.exists_mem_ne htwo a
  refine ⟨b, hbS, hba, ?_⟩
  intro hbLeaf
  exact hba (hunique b hbS hbLeaf)

/-- In the unique-leaf state, choose a nonleaf exit and construct a complete
pairing which forces the leaf to use that exit. -/
theorem exists_mate_with_unique_leaf_owner_exit
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (leaf : V → Prop) (a : V)
    (heven : Even S.card) (haS : a ∈ S) (haLeaf : leaf a)
    (hunique : ∀ x ∈ S, leaf x → x = a) :
    ∃ b ∈ S, b ≠ a ∧ ¬ leaf b ∧
      ∃ mate : V → V,
        mate a = b ∧ mate b = a ∧
        (∀ x, x ∈ S → mate x ∈ S) ∧
        (∀ x, x ∈ S → mate (mate x) = x) ∧
        (∀ x, x ∈ S → mate x ≠ x) ∧
        ∀ x, x ∉ S → mate x = x := by
  obtain ⟨b, hbS, hba, hbLeaf⟩ :=
    exists_nonleaf_of_even_of_unique_leaf S leaf a
      heven haS haLeaf hunique
  obtain ⟨mate, hab, hba', hclosed, hinvol, hfixed, houtside⟩ :=
    exists_mate_of_even_finset_with_prescribed_pair
      S a b heven hba.symm haS hbS
  exact ⟨b, hbS, hba, hbLeaf, mate, hab, hba',
    hclosed, hinvol, hfixed, houtside⟩

/-- In the two-leaf state, pair the two leaves together.  Every remaining
pair then consists entirely of nonleaves. -/
theorem exists_mate_with_two_leaf_owner_through
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (leaf : V → Prop) (a b : V)
    (heven : Even S.card) (hab : a ≠ b)
    (haS : a ∈ S) (hbS : b ∈ S)
    (_haLeaf : leaf a) (_hbLeaf : leaf b)
    (hleaves : ∀ x ∈ S, leaf x → x = a ∨ x = b) :
    ∃ mate : V → V,
      mate a = b ∧ mate b = a ∧
      (∀ x, x ∈ S → mate x ∈ S) ∧
      (∀ x, x ∈ S → mate (mate x) = x) ∧
      (∀ x, x ∈ S → mate x ≠ x) ∧
      (∀ x, x ∉ S → mate x = x) ∧
      ∀ x ∈ S, x ≠ a → x ≠ b →
        ¬ leaf x ∧ ¬ leaf (mate x) := by
  obtain ⟨mate, hma, hmb, hclosed, hinvol, hfixed, houtside⟩ :=
    exists_mate_of_even_finset_with_prescribed_pair
      S a b heven hab haS hbS
  refine ⟨mate, hma, hmb, hclosed, hinvol, hfixed, houtside, ?_⟩
  intro x hxS hxa hxb
  have hxNonleaf : ¬ leaf x := by
    intro hxLeaf
    rcases hleaves x hxS hxLeaf with h | h
    · exact hxa h
    · exact hxb h
  have hmS := hclosed x hxS
  have hma' : mate x ≠ a := by
    intro h
    have hh := congrArg mate h
    rw [hinvol x hxS, hma] at hh
    exact hxb hh
  have hmb' : mate x ≠ b := by
    intro h
    have hh := congrArg mate h
    rw [hinvol x hxS, hmb] at hh
    exact hxa hh
  have hmNonleaf : ¬ leaf (mate x) := by
    intro hmLeaf
    rcases hleaves (mate x) hmS hmLeaf with h | h
    · exact hma' h
    · exact hmb' h
  exact ⟨hxNonleaf, hmNonleaf⟩

#print axioms exists_nonleaf_of_even_of_unique_leaf
#print axioms exists_mate_with_unique_leaf_owner_exit
#print axioms exists_mate_with_two_leaf_owner_through

end

end Erdos85
