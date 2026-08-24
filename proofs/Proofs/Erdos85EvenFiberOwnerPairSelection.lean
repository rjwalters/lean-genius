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

#print axioms exists_nonleaf_of_even_of_unique_leaf
#print axioms exists_mate_with_unique_leaf_owner_exit

end

end Erdos85
