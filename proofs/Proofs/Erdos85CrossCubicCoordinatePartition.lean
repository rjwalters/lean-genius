import Proofs.Erdos85CrossCubicExceptionalCoordinates

/-! # The `4/4/8` cubic-coordinate partition for a cross target -/

open Finset

namespace Erdos85

noncomputable section

def h305CubicOffsetOneCoordinates (i : ZMod 8) : Finset (ZMod 8) :=
  {i - 1, i + 1}

def h305CubicOffsetThreeCoordinates (i : ZMod 8) : Finset (ZMod 8) :=
  {i - 3, i + 3}

def h305CubicRemainingCoordinates (i : ZMod 8) : Finset (ZMod 8) :=
  Finset.univ \ (h305CubicOffsetOneCoordinates i ∪
    h305CubicOffsetThreeCoordinates i)

set_option maxRecDepth 100000 in
theorem h305CubicCoordinatePartition_finiteFacts :
    ∀ i : ZMod 8,
      (h305CubicOffsetOneCoordinates i).card = 2 ∧
      (h305CubicOffsetThreeCoordinates i).card = 2 ∧
      (h305CubicRemainingCoordinates i).card = 4 ∧
      Disjoint (h305CubicOffsetOneCoordinates i)
        (h305CubicOffsetThreeCoordinates i) ∧
      Disjoint (h305CubicOffsetOneCoordinates i)
        (h305CubicRemainingCoordinates i) ∧
      Disjoint (h305CubicOffsetThreeCoordinates i)
        (h305CubicRemainingCoordinates i) ∧
      h305CubicOffsetOneCoordinates i ∪
          h305CubicOffsetThreeCoordinates i ∪
          h305CubicRemainingCoordinates i = Finset.univ := by
  native_decide

def h305CrossCubicOffsetOneVertices
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305CubicOffsetOneCoordinates i).image u ∪
    (h305CubicOffsetOneCoordinates j).image v

def h305CrossCubicOffsetThreeVertices
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305CubicOffsetThreeCoordinates i).image u ∪
    (h305CubicOffsetThreeCoordinates j).image v

def h305CrossCubicRemainingVertices
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305CubicRemainingCoordinates i).image u ∪
    (h305CubicRemainingCoordinates j).image v

private theorem image_union_card
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v) (hdisj : ∀ k l, u k ≠ v l)
    (A B : Finset (ZMod 8)) :
    (A.image u ∪ B.image v).card = A.card + B.card := by
  have hd : Disjoint (A.image u) (B.image v) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rcases Finset.mem_image.mp hxA with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hxB with ⟨l, hl, h⟩
    exact hdisj k l h.symm
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ huinj,
    Finset.card_image_of_injective _ hvinj]

private theorem shore_image_unions_disjoint
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v) (hdisj : ∀ k l, u k ≠ v l)
    (A B C D : Finset (ZMod 8))
    (hAC : Disjoint A C) (hBD : Disjoint B D) :
    Disjoint (A.image u ∪ B.image v) (C.image u ∪ D.image v) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact Finset.disjoint_left.mp hAC hk (huinj h ▸ hl)
  · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact hdisj k l h.symm
  · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact hdisj l k h
  · rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact Finset.disjoint_left.mp hBD hk (hvinj h ▸ hl)

/-- The cross-target coordinate classes have populations `4`, `4`, and
`8`, are pairwise disjoint, and cover the ambient sixteen vertices. -/
theorem h305CrossCubicCoordinatePartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v) (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (i j : ZMod 8) :
    let X25 := h305CrossCubicOffsetOneVertices u v i j
    let X16 := h305CrossCubicOffsetThreeVertices u v i j
    let X17 := h305CrossCubicRemainingVertices u v i j
    X25.card = 4 ∧ X16.card = 4 ∧ X17.card = 8 ∧
      Disjoint X25 X16 ∧ Disjoint X25 X17 ∧ Disjoint X16 X17 ∧
      X25 ∪ X16 ∪ X17 = Finset.univ := by
  classical
  dsimp only
  obtain ⟨hi1, hi3, hir, hi13, hi1r, hi3r, hicover⟩ :=
    h305CubicCoordinatePartition_finiteFacts i
  obtain ⟨hj1, hj3, hjr, hj13, hj1r, hj3r, hjcover⟩ :=
    h305CubicCoordinatePartition_finiteFacts j
  have h25card : (h305CrossCubicOffsetOneVertices u v i j).card = 4 := by
    rw [h305CrossCubicOffsetOneVertices,
      image_union_card u v huinj hvinj hdisj]
    omega
  have h16card : (h305CrossCubicOffsetThreeVertices u v i j).card = 4 := by
    rw [h305CrossCubicOffsetThreeVertices,
      image_union_card u v huinj hvinj hdisj]
    omega
  have h17card : (h305CrossCubicRemainingVertices u v i j).card = 8 := by
    rw [h305CrossCubicRemainingVertices,
      image_union_card u v huinj hvinj hdisj]
    omega
  have h2516 : Disjoint (h305CrossCubicOffsetOneVertices u v i j)
      (h305CrossCubicOffsetThreeVertices u v i j) := by
    exact shore_image_unions_disjoint u v huinj hvinj hdisj _ _ _ _ hi13 hj13
  have h2517 : Disjoint (h305CrossCubicOffsetOneVertices u v i j)
      (h305CrossCubicRemainingVertices u v i j) := by
    exact shore_image_unions_disjoint u v huinj hvinj hdisj _ _ _ _ hi1r hj1r
  have h1617 : Disjoint (h305CrossCubicOffsetThreeVertices u v i j)
      (h305CrossCubicRemainingVertices u v i j) := by
    exact shore_image_unions_disjoint u v huinj hvinj hdisj _ _ _ _ hi3r hj3r
  have hvertexCover : h305CrossCubicOffsetOneVertices u v i j ∪
      h305CrossCubicOffsetThreeVertices u v i j ∪
      h305CrossCubicRemainingVertices u v i j = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hcover x with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hk : k ∈ h305CubicOffsetOneCoordinates i ∪
          h305CubicOffsetThreeCoordinates i ∪
          h305CubicRemainingCoordinates i := by rw [hicover]; simp
      rcases Finset.mem_union.mp hk with hk | hk
      · rcases Finset.mem_union.mp hk with hk | hk
        · exact Or.inl (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_image.mpr ⟨k, hk, rfl⟩))))
        · exact Or.inl (Or.inr (Finset.mem_union.mpr
            (Or.inl (Finset.mem_image.mpr ⟨k, hk, rfl⟩))))
      · exact Or.inr (Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨k, hk, rfl⟩)))
    · have hk : k ∈ h305CubicOffsetOneCoordinates j ∪
          h305CubicOffsetThreeCoordinates j ∪
          h305CubicRemainingCoordinates j := by rw [hjcover]; simp
      rcases Finset.mem_union.mp hk with hk | hk
      · rcases Finset.mem_union.mp hk with hk | hk
        · exact Or.inl (Or.inl (Finset.mem_union.mpr
            (Or.inr (Finset.mem_image.mpr ⟨k, hk, rfl⟩))))
        · exact Or.inl (Or.inr (Finset.mem_union.mpr
            (Or.inr (Finset.mem_image.mpr ⟨k, hk, rfl⟩))))
      · exact Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨k, hk, rfl⟩)))
  exact ⟨h25card, h16card, h17card, h2516, h2517, h1617, hvertexCover⟩

end

end Erdos85

#print axioms Erdos85.h305CubicCoordinatePartition_finiteFacts
#print axioms Erdos85.h305CrossCubicCoordinatePartition
