import Proofs.Erdos85CubicResidualRowExcessBridge
import Proofs.Erdos85EdgeIndexedServiceCubicEightCycleCensus

/-! # Cubic fiber bounds for same-shore nonantipodal targets -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def eightCycleSingleEndpointCubeValue (k i : ZMod 8) : ℕ :=
  if i = k - 1 ∨ i = k + 1 then 3
  else if i = k - 3 ∨ i = k + 3 then 1 else 0

def eightCycleEndpointPairCubeValue (k i j : ZMod 8) : ℕ :=
  eightCycleSingleEndpointCubeValue k i +
    eightCycleSingleEndpointCubeValue k j

def h305SameShoreCubicBudget25Coordinates (i j : ZMod 8) :
    Finset (ZMod 8) :=
  Finset.univ.filter fun k ↦ eightCycleEndpointPairCubeValue k i j = 3

def h305SameShoreCubicBudget27Coordinates (i j : ZMod 8) :
    Finset (ZMod 8) :=
  Finset.univ.filter fun k ↦ eightCycleEndpointPairCubeValue k i j = 1

set_option maxRecDepth 100000 in
theorem h305SameShore_nonantipodal_coordinate_finiteFacts :
    ∀ i j : ZMod 8,
      (j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) →
      (h305SameShoreCubicBudget25Coordinates i j).card = 4 ∧
      (h305SameShoreCubicBudget27Coordinates i j).card = 4 ∧
      Disjoint (h305SameShoreCubicBudget25Coordinates i j)
        (h305SameShoreCubicBudget27Coordinates i j) ∧
      h305SameShoreCubicBudget25Coordinates i j ∪
        h305SameShoreCubicBudget27Coordinates i j = Finset.univ := by
  native_decide

def h305SameShoreCubicBudget25Vertices
    {V : Type*} [DecidableEq V]
    (u : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305SameShoreCubicBudget25Coordinates i j).image u

def h305SameShoreCubicBudget16Vertices
    {V : Type*} [DecidableEq V]
    (u : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305SameShoreCubicBudget27Coordinates i j).image u

def h305SameShoreCubicBudget17Vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : ZMod 8 → V) : Finset V :=
  Finset.univ.image v

/-- For a nonantipodal same-shore target, the four coordinates receiving
internal cubic mass three, the four receiving mass one, and all eight
coordinates on the other shore form the required `4/4/8` partition. -/
theorem h305SameShore_nonantipodal_cubicCoordinatePartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v) (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (i j : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) :
    let X25 := h305SameShoreCubicBudget25Vertices u i j
    let X16 := h305SameShoreCubicBudget16Vertices u i j
    let X17 := h305SameShoreCubicBudget17Vertices v
    X25.card = 4 ∧ X16.card = 4 ∧ X17.card = 8 ∧
      Disjoint X25 X16 ∧ Disjoint X25 X17 ∧ Disjoint X16 X17 ∧
      X25 ∪ X16 ∪ X17 = Finset.univ := by
  classical
  dsimp only
  obtain ⟨h25c, h16c, hdcoord, hcoordcover⟩ :=
    h305SameShore_nonantipodal_coordinate_finiteFacts i j hodd
  have h25card : (h305SameShoreCubicBudget25Vertices u i j).card = 4 := by
    rw [h305SameShoreCubicBudget25Vertices,
      Finset.card_image_of_injective _ huinj, h25c]
  have h16card : (h305SameShoreCubicBudget16Vertices u i j).card = 4 := by
    rw [h305SameShoreCubicBudget16Vertices,
      Finset.card_image_of_injective _ huinj, h16c]
  have h17card : (h305SameShoreCubicBudget17Vertices v).card = 8 := by
    rw [h305SameShoreCubicBudget17Vertices,
      Finset.card_image_of_injective _ hvinj]
    simp
  have h2516 : Disjoint (h305SameShoreCubicBudget25Vertices u i j)
      (h305SameShoreCubicBudget16Vertices u i j) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, hkl⟩
    exact Finset.disjoint_left.mp hdcoord hk (huinj hkl ▸ hl)
  have h2517 : Disjoint (h305SameShoreCubicBudget25Vertices u i j)
      (h305SameShoreCubicBudget17Vertices v) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact hdisj k l h.symm
  have h1617 : Disjoint (h305SameShoreCubicBudget16Vertices u i j)
      (h305SameShoreCubicBudget17Vertices v) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact hdisj k l h.symm
  have hfull : h305SameShoreCubicBudget25Vertices u i j ∪
      h305SameShoreCubicBudget16Vertices u i j ∪
      h305SameShoreCubicBudget17Vertices v = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hcover x with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hk : k ∈ h305SameShoreCubicBudget25Coordinates i j ∪
          h305SameShoreCubicBudget27Coordinates i j := by
        rw [hcoordcover]
        simp
      rcases Finset.mem_union.mp hk with hk | hk
      · exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
      · exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
    · exact Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  exact ⟨h25card, h16card, h17card, h2516, h2517, h1617, hfull⟩

end

end Erdos85

#print axioms Erdos85.h305SameShore_nonantipodal_coordinate_finiteFacts
#print axioms Erdos85.h305SameShore_nonantipodal_cubicCoordinatePartition
