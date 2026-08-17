import Proofs.Erdos85DegreeTwoRepeatedForkSaturation

/-! # Packing isolated bipartite owner blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two nonempty bipartite blocks whose rows alternate exactly between their
two sides are either the same vertex block or disjoint. -/
theorem alternatingNeighborBlocks_eq_or_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (L₁ R₁ L₂ R₂ : Finset V)
    (hL₁ : L₁.Nonempty) (hR₁ : R₁.Nonempty)
    (_hL₂ : L₂.Nonempty) (_hR₂ : R₂.Nonempty)
    (h₁L : ∀ u ∈ L₁, H.neighborFinset u = R₁)
    (h₁R : ∀ u ∈ R₁, H.neighborFinset u = L₁)
    (h₂L : ∀ u ∈ L₂, H.neighborFinset u = R₂)
    (h₂R : ∀ u ∈ R₂, H.neighborFinset u = L₂) :
    L₁ ∪ R₁ = L₂ ∪ R₂ ∨ Disjoint (L₁ ∪ R₁) (L₂ ∪ R₂) := by
  by_cases hd : Disjoint (L₁ ∪ R₁) (L₂ ∪ R₂)
  · exact Or.inr hd
  · left
    obtain ⟨u, hu₁, hu₂⟩ := Finset.not_disjoint_iff.mp hd
    rcases Finset.mem_union.mp hu₁ with huL₁ | huR₁ <;>
      rcases Finset.mem_union.mp hu₂ with huL₂ | huR₂
    · have hR : R₁ = R₂ := (h₁L u huL₁).symm.trans (h₂L u huL₂)
      obtain ⟨v, hvR₁⟩ := hR₁
      have hvR₂ : v ∈ R₂ := by simpa [hR] using hvR₁
      have hL : L₁ = L₂ := (h₁R v hvR₁).symm.trans (h₂R v hvR₂)
      rw [hL, hR]
    · have hR₁L₂ : R₁ = L₂ := (h₁L u huL₁).symm.trans (h₂R u huR₂)
      obtain ⟨v, hvR₁⟩ := hR₁
      have hvL₂ : v ∈ L₂ := by simpa [hR₁L₂] using hvR₁
      have hL₁R₂ : L₁ = R₂ := (h₁R v hvR₁).symm.trans (h₂L v hvL₂)
      rw [hL₁R₂, hR₁L₂, Finset.union_comm]
    · have hL₁R₂ : L₁ = R₂ := (h₁R u huR₁).symm.trans (h₂L u huL₂)
      obtain ⟨v, hvL₁⟩ := hL₁
      have hvR₂ : v ∈ R₂ := by simpa [hL₁R₂] using hvL₁
      have hR₁L₂ : R₁ = L₂ := (h₁L v hvL₁).symm.trans (h₂R v hvR₂)
      rw [hL₁R₂, hR₁L₂, Finset.union_comm]
    · have hL : L₁ = L₂ := (h₁R u huR₁).symm.trans (h₂R u huR₂)
      obtain ⟨v, hvL₁⟩ := hL₁
      have hvL₂ : v ∈ L₂ := by simpa [hL] using hvL₁
      have hR : R₁ = R₂ := (h₁L v hvL₁).symm.trans (h₂L v hvL₂)
      rw [hL, hR]

/-- Consequently, two isolated `K₂,₂` neighborhood normal forms in the same
graph have equal four-vertex supports or disjoint supports. -/
theorem isolatedK22_blocks_eq_or_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {x₁ y₁ r₁ s₁ x₂ y₂ r₂ s₂ : V}
    (hx₁ : H.neighborFinset x₁ = {r₁, s₁})
    (hy₁ : H.neighborFinset y₁ = {r₁, s₁})
    (hr₁ : H.neighborFinset r₁ = {x₁, y₁})
    (hs₁ : H.neighborFinset s₁ = {x₁, y₁})
    (hx₂ : H.neighborFinset x₂ = {r₂, s₂})
    (hy₂ : H.neighborFinset y₂ = {r₂, s₂})
    (hr₂ : H.neighborFinset r₂ = {x₂, y₂})
    (hs₂ : H.neighborFinset s₂ = {x₂, y₂}) :
    ({x₁, y₁, r₁, s₁} : Finset V) = {x₂, y₂, r₂, s₂} ∨
      Disjoint ({x₁, y₁, r₁, s₁} : Finset V) {x₂, y₂, r₂, s₂} := by
  have h := alternatingNeighborBlocks_eq_or_disjoint H
    ({x₁, y₁} : Finset V) {r₁, s₁} {x₂, y₂} {r₂, s₂}
    (by simp) (by simp) (by simp) (by simp)
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu;
        rcases hu with rfl | rfl <;> assumption)
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu;
        rcases hu with rfl | rfl <;> assumption)
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu;
        rcases hu with rfl | rfl <;> assumption)
    (by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu;
        rcases hu with rfl | rfl <;> assumption)
  have hB₁ : ({x₁, y₁} : Finset V) ∪ {r₁, s₁} = {x₁, y₁, r₁, s₁} := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hB₂ : ({x₂, y₂} : Finset V) ∪ {r₂, s₂} = {x₂, y₂, r₂, s₂} := by
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hB₁, hB₂] at h
  exact h

/-- At most four distinct cardinality-four owner blocks fit in a sixteen-point
factor once the preceding equal-or-disjoint property has identified duplicate
witnesses. -/
theorem card_ownerBlocks_le_four_of_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 16)
    (blocks : Finset (Finset V))
    (hcard : ∀ S ∈ blocks, S.card = 4)
    (hdisj : ∀ S ∈ blocks, ∀ T ∈ blocks, S ≠ T → Disjoint S T) :
    blocks.card ≤ 4 := by
  have hunionLe : (blocks.biUnion id).card ≤ 16 := by
    calc
      (blocks.biUnion id).card ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 16 := by simpa using hV
  have hunion : (blocks.biUnion id).card = ∑ S ∈ blocks, S.card := by
    have hpair : ∀ S ∈ blocks, ∀ T ∈ blocks, S ≠ T → Disjoint (id S) (id T) := by
      intro S hS T hT hne
      exact hdisj S hS T hT hne
    rw [Finset.card_biUnion hpair]
    simp
  rw [hunion] at hunionLe
  have hsum : (∑ S ∈ blocks, S.card) = blocks.card * 4 := by
    calc
      (∑ S ∈ blocks, S.card) = ∑ _S ∈ blocks, 4 := by
        apply Finset.sum_congr rfl
        intro S hS
        exact hcard S hS
      _ = blocks.card * 4 := by simp
  rw [hsum] at hunionLe
  omega

end

end Erdos85
