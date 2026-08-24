import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Pure-ordinary forced mate relays

This file isolates the finite graph geometry used in `(73rnz_cl)`.  If a
center sees exactly two selected points and one of them is the marked
endpoint, there is a unique other selected point.  For two pole endpoints,
zero common-neighbor codegree of the poles also forces their centers to be
distinct.
-/

open SimpleGraph

namespace Erdos85

/-- The selected points on the line represented by `a`. -/
def selectedNeighborFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X : Finset V) (a : V) : Finset V :=
  A.neighborFinset a ∩ X

/-- **Forced mate relay (`73rnz_cl`).**  A marked point in a two-point
selected neighbor fiber has a unique distinct mate in that fiber. -/
theorem existsUnique_selected_neighbor_mate_of_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X : Finset V) (a p : V)
    (hpX : p ∈ X) (hap : A.Adj a p)
    (hcard : (selectedNeighborFiber A X a).card = 2) :
    ∃! z : V, z ∈ X ∧ A.Adj a z ∧ z ≠ p := by
  let S := selectedNeighborFiber A X a
  have hpS : p ∈ S := by
    simp [S, selectedNeighborFiber, hpX, hap]
  have herase : (S.erase p).card = 1 := by
    rw [Finset.card_erase_of_mem hpS, hcard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp herase
  have hzmem : z ∈ S.erase p := by simp [hz]
  refine ⟨z, ?_, ?_⟩
  · have hzS := (Finset.mem_erase.mp hzmem).2
    exact ⟨(Finset.mem_inter.mp hzS).2,
      (A.mem_neighborFinset a z).mp (Finset.mem_inter.mp hzS).1,
      (Finset.mem_erase.mp hzmem).1⟩
  · intro w hw
    have hwS : w ∈ S := by
      exact Finset.mem_inter.mpr
        ⟨(A.mem_neighborFinset a w).mpr hw.2.1, hw.1⟩
    have hwErase : w ∈ S.erase p := Finset.mem_erase.mpr ⟨hw.2.2, hwS⟩
    simpa [hz] using hwErase

/-- The two forced mate relays at distinct poles have distinct centers when
the poles have no common `A`-neighbor. -/
theorem existsUnique_two_forced_mates_and_centers_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X : Finset V) (E₁ E₂ a₁ a₂ p₁ p₂ : V)
    (hE₁a₁ : A.Adj E₁ a₁) (hE₂a₂ : A.Adj E₂ a₂)
    (hcodeg : ∀ a, ¬ (A.Adj E₁ a ∧ A.Adj E₂ a))
    (hp₁X : p₁ ∈ X) (ha₁p₁ : A.Adj a₁ p₁)
    (hp₂X : p₂ ∈ X) (ha₂p₂ : A.Adj a₂ p₂)
    (hcard₁ : (selectedNeighborFiber A X a₁).card = 2)
    (hcard₂ : (selectedNeighborFiber A X a₂).card = 2) :
    a₁ ≠ a₂ ∧
      (∃! z₁ : V, z₁ ∈ X ∧ A.Adj a₁ z₁ ∧ z₁ ≠ p₁) ∧
      (∃! z₂ : V, z₂ ∈ X ∧ A.Adj a₂ z₂ ∧ z₂ ≠ p₂) := by
  refine ⟨?_,
    existsUnique_selected_neighbor_mate_of_card_two A X a₁ p₁ hp₁X ha₁p₁ hcard₁,
    existsUnique_selected_neighbor_mate_of_card_two A X a₂ p₂ hp₂X ha₂p₂ hcard₂⟩
  intro h
  subst a₂
  exact hcodeg a₁ ⟨hE₁a₁, hE₂a₂⟩

end Erdos85

#print axioms Erdos85.existsUnique_selected_neighbor_mate_of_card_two
#print axioms Erdos85.existsUnique_two_forced_mates_and_centers_ne
