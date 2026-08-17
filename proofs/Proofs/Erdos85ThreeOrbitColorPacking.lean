import Proofs.Erdos85ThreeColorFiberSharpBoundary

/-! # Three orbit color packing -/

namespace Erdos85

/-- Three nonempty color sets packed into a three-color palette either overlap
between two orbits, or are singleton sets partitioning the palette. -/
theorem three_nonempty_colorSets_overlap_or_singleton_partition
    {C : Type*} [DecidableEq C]
    (palette A B C₀ : Finset C)
    (hpalette : palette.card = 3)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C₀.Nonempty)
    (hAsub : A ⊆ palette) (hBsub : B ⊆ palette)
    (hCsub : C₀ ⊆ palette) :
    ¬Disjoint A B ∨ ¬Disjoint A C₀ ∨ ¬Disjoint B C₀ ∨
      (A.card = 1 ∧ B.card = 1 ∧ C₀.card = 1 ∧
        (A ∪ B) ∪ C₀ = palette) := by
  by_cases hAB : Disjoint A B
  · by_cases hAC : Disjoint A C₀
    · by_cases hBC : Disjoint B C₀
      · right
        right
        right
        have hABC : Disjoint (A ∪ B) C₀ := by
          rw [Finset.disjoint_union_left]
          exact ⟨hAC, hBC⟩
        have hsub : (A ∪ B) ∪ C₀ ⊆ palette := by
          intro c hc
          simp only [Finset.mem_union] at hc
          rcases hc with (hc | hc) | hc
          · exact hAsub hc
          · exact hBsub hc
          · exact hCsub hc
        have hcardUnion : ((A ∪ B) ∪ C₀).card =
            A.card + B.card + C₀.card := by
          rw [Finset.card_union_of_disjoint hABC,
            Finset.card_union_of_disjoint hAB]
        have hAle : 1 ≤ A.card := Finset.card_pos.mpr hA
        have hBle : 1 ≤ B.card := Finset.card_pos.mpr hB
        have hCle : 1 ≤ C₀.card := Finset.card_pos.mpr hC
        have htotal : A.card + B.card + C₀.card ≤ 3 := by
          rw [← hcardUnion, ← hpalette]
          exact Finset.card_le_card hsub
        have hAc : A.card = 1 := by omega
        have hBc : B.card = 1 := by omega
        have hCc : C₀.card = 1 := by omega
        refine ⟨hAc, hBc, hCc, Finset.eq_of_subset_of_card_le hsub ?_⟩
        rw [hcardUnion, hAc, hBc, hCc, hpalette]
      · exact Or.inr (Or.inr (Or.inl hBC))
    · exact Or.inr (Or.inl hAC)
  · exact Or.inl hAB

end Erdos85
