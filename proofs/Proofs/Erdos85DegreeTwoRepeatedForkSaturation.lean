import Mathlib

/-! # A repeated fork saturates a two-regular graph row -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two distinct specified neighbors exhaust the neighborhood of a vertex of
degree two. -/
theorem degreeTwo_neighborFinset_eq_pair_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {x r₁ r₂ : V} (hr : r₁ ≠ r₂)
    (h₁ : H.Adj x r₁) (h₂ : H.Adj x r₂) :
    H.neighborFinset x = {r₁, r₂} := by
  have hsub : {r₁, r₂} ⊆ H.neighborFinset x := by
    intro r hrmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrmem
    rcases hrmem with rfl | rfl
    · exact (H.mem_neighborFinset x _).mpr h₁
    · exact (H.mem_neighborFinset x _).mpr h₂
  have hcardN : (H.neighborFinset x).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg x]
  have hcardPair : ({r₁, r₂} : Finset V).card = 2 := by simp [hr]
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- A repeated fork in a two-regular graph forces the two fork tips to have
identical, completely saturated neighborhood rows. -/
theorem degreeTwo_repeatedFork_neighborFinset_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {x y r₁ r₂ : V} (hr : r₁ ≠ r₂)
    (hxr₁ : H.Adj x r₁) (hyr₁ : H.Adj y r₁)
    (hxr₂ : H.Adj x r₂) (hyr₂ : H.Adj y r₂) :
    H.neighborFinset x = H.neighborFinset y := by
  rw [degreeTwo_neighborFinset_eq_pair_of_adj H hdeg hr hxr₁ hxr₂,
    degreeTwo_neighborFinset_eq_pair_of_adj H hdeg hr hyr₁ hyr₂]

/-- Integral adjacency-matrix row form of repeated-fork saturation. -/
theorem degreeTwo_repeatedFork_adjMatrix_rows_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {x y r₁ r₂ : V} (hr : r₁ ≠ r₂)
    (hxr₁ : H.Adj x r₁) (hyr₁ : H.Adj y r₁)
    (hxr₂ : H.Adj x r₂) (hyr₂ : H.Adj y r₂) :
    ∀ z : V, H.adjMatrix ℤ x z = H.adjMatrix ℤ y z := by
  have hN := degreeTwo_repeatedFork_neighborFinset_eq
    H hdeg hr hxr₁ hyr₁ hxr₂ hyr₂
  intro z
  rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
  have hz : H.Adj x z ↔ H.Adj y z := by
    rw [← H.mem_neighborFinset, ← H.mem_neighborFinset, hN]
  by_cases hxz : H.Adj x z
  · rw [if_pos hxz, if_pos (hz.mp hxz)]
  · rw [if_neg hxz, if_neg (fun hyz => hxz (hz.mpr hyz))]

/-- Full isolated `K₂,₂` normal form forced by a repeated fork.  Since every
one of the four vertices already has its two prescribed neighbors, the block
has no edges leaving it. -/
theorem degreeTwo_repeatedFork_isolatedK22
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {x y r₁ r₂ : V} (hxy : x ≠ y) (hr : r₁ ≠ r₂)
    (hxr₁ : H.Adj x r₁) (hyr₁ : H.Adj y r₁)
    (hxr₂ : H.Adj x r₂) (hyr₂ : H.Adj y r₂) :
    H.neighborFinset x = {r₁, r₂} ∧
      H.neighborFinset y = {r₁, r₂} ∧
      H.neighborFinset r₁ = {x, y} ∧
      H.neighborFinset r₂ = {x, y} := by
  refine ⟨
    degreeTwo_neighborFinset_eq_pair_of_adj H hdeg hr hxr₁ hxr₂,
    degreeTwo_neighborFinset_eq_pair_of_adj H hdeg hr hyr₁ hyr₂,
    degreeTwo_neighborFinset_eq_pair_of_adj H hdeg hxy hxr₁.symm hyr₁.symm,
    degreeTwo_neighborFinset_eq_pair_of_adj H hdeg hxy hxr₂.symm hyr₂.symm⟩

/-- The four vertices of a repeated fork form a cardinality-four set closed
under taking graph neighbors.  This is the counting interface for packing
several forced owner blocks into a sixteen-vertex factor. -/
theorem degreeTwo_repeatedFork_closed_card_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ z, H.degree z = 2)
    {x y r₁ r₂ : V} (hxy : x ≠ y) (hr : r₁ ≠ r₂)
    (hxr₁ : H.Adj x r₁) (hyr₁ : H.Adj y r₁)
    (hxr₂ : H.Adj x r₂) (hyr₂ : H.Adj y r₂) :
    let S : Finset V := {x, y, r₁, r₂}
    S.card = 4 ∧ ∀ u ∈ S, H.neighborFinset u ⊆ S := by
  classical
  let S : Finset V := {x, y, r₁, r₂}
  obtain ⟨hx, hy, hr₁, hr₂⟩ := degreeTwo_repeatedFork_isolatedK22
    H hdeg hxy hr hxr₁ hyr₁ hxr₂ hyr₂
  have hxr₁ne : x ≠ r₁ := H.ne_of_adj hxr₁
  have hxr₂ne : x ≠ r₂ := H.ne_of_adj hxr₂
  have hyr₁ne : y ≠ r₁ := H.ne_of_adj hyr₁
  have hyr₂ne : y ≠ r₂ := H.ne_of_adj hyr₂
  refine ⟨?_, ?_⟩
  · simp [hxy, hr, hxr₁ne, hxr₂ne, hyr₁ne, hyr₂ne]
  · intro u hu v hv
    change u ∈ ({x, y, r₁, r₂} : Finset V) at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl
    · rw [hx] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      aesop
    · rw [hy] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      aesop
    · rw [hr₁] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      aesop
    · rw [hr₂] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      aesop

end

end Erdos85
