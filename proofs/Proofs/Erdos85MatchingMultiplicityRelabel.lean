import Proofs.Erdos85OddKeyLabelGraph

/-! # Relabeling invariance of unordered matching-key multiplicity -/

namespace Erdos85

noncomputable section

theorem canonicalOrderedPair_eq_iff
    {L : Type*} [LinearOrder L] (a b c d : L) :
    (min a b, max a b) = (min c d, max c d) ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases le_total a b with hab | hba <;>
    rcases le_total c d with hcd | hdc
  · simp only [min_eq_left hab, max_eq_right hab,
      min_eq_left hcd, max_eq_right hcd, Prod.mk.injEq]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · have hba' : b ≤ a := by simpa [h.1, h.2] using hcd
        have heq : a = b := le_antisymm hab hba'
        exact ⟨heq.trans h.2, heq.symm.trans h.1⟩
  · simp only [min_eq_left hab, max_eq_right hab,
      min_eq_right hdc, max_eq_left hdc, Prod.mk.injEq]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · have hba' : b ≤ a := by simpa [h.1, h.2] using hdc
        have heq : a = b := le_antisymm hab hba'
        exact ⟨heq.trans h.2, heq.symm.trans h.1⟩
      · exact h
  · simp only [min_eq_right hba, max_eq_left hba,
      min_eq_left hcd, max_eq_right hcd, Prod.mk.injEq]
    constructor
    · intro h
      exact Or.inr ⟨h.2, h.1⟩
    · rintro (h | h)
      · have hab' : a ≤ b := by simpa [h.1, h.2] using hcd
        have heq : b = a := le_antisymm hba hab'
        exact ⟨heq.trans h.1, heq.symm.trans h.2⟩
      · exact ⟨h.2, h.1⟩
  · simp only [min_eq_right hba, max_eq_left hba,
      min_eq_right hdc, max_eq_left hdc, Prod.mk.injEq]
    constructor
    · intro h
      exact Or.inl ⟨h.2, h.1⟩
    · rintro (h | h)
      · exact ⟨h.2, h.1⟩
      · have hab' : a ≤ b := by simpa [h.1, h.2] using hdc
        have heq : b = a := le_antisymm hba hab'
        exact ⟨heq.trans h.1, heq.symm.trans h.2⟩

theorem canonicalOrderedPair_equiv_eq_iff
    {L M : Type*} [LinearOrder L] [LinearOrder M]
    (e : L ≃ M) (a b c d : L) :
    (min (e a) (e b), max (e a) (e b)) =
        (min (e c) (e d), max (e c) (e d)) ↔
      (min a b, max a b) = (min c d, max c d) := by
  rw [canonicalOrderedPair_eq_iff, canonicalOrderedPair_eq_iff]
  simp only [e.injective.eq_iff]

/-- Applying any equivalence to all labels preserves the multiplicity of the
corresponding unordered pair.  No order-preservation assumption is needed:
each side canonicalizes using its own linear order. -/
theorem exchangedMissPairMultiplicity_equiv
    {X L M : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    [Fintype M] [DecidableEq M] [LinearOrder M]
    (mate : X → X) (label : X → L) (e : L ≃ M) (a b : L) :
    exchangedMissPairMultiplicity mate (e ∘ label)
        (min (e a) (e b), max (e a) (e b)) =
      exchangedMissPairMultiplicity mate label
        (min a b, max a b) := by
  classical
  have hsources : nonconstantMatchingEdgeSources mate (e ∘ label) =
      nonconstantMatchingEdgeSources mate label := by
    ext x
    simp [nonconstantMatchingEdgeSources, Function.comp_apply,
      e.injective.eq_iff]
  unfold exchangedMissPairMultiplicity
  rw [hsources]
  congr 1
  ext x
  simp only [Finset.mem_filter, Function.comp_apply, exchangedMissPairKey]
  rw [canonicalOrderedPair_equiv_eq_iff e
    (label x) (label (mate x)) a b]

/-- Consequently the equivalence on labels is an exact adjacency transport
between the two odd exchanged-key support graphs. -/
theorem oddExchangedKeyLabelGraph_adj_equiv
    {X L M : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    [Fintype M] [DecidableEq M] [LinearOrder M]
    (mate : X → X) (label : X → L) (e : L ≃ M) (a b : L) :
    (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity mate (e ∘ label))).Adj (e a) (e b) ↔
    (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity mate label)).Adj a b := by
  constructor
  · rintro ⟨hne, hodd⟩
    refine ⟨fun hab => hne (congrArg e hab), ?_⟩
    rw [exchangedMissPairMultiplicity_equiv mate label e a b] at hodd
    exact hodd
  · rintro ⟨hne, hodd⟩
    refine ⟨fun hab => hne (e.injective hab), ?_⟩
    rw [exchangedMissPairMultiplicity_equiv mate label e a b]
    exact hodd

end

end Erdos85
