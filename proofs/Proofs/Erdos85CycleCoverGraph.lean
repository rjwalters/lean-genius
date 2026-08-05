import Proofs.Erdos85CycleCoverRigidity
import Proofs.Erdos85MixedAnchorSupport

/-!
# Graph-facing cyclic-cover rigidity

This file turns a quotient entry equal to one into the actual coordinate
map between two labeled defect cycles.  Commutation with the defect
two-factor then makes the selector locally intertwine the two cycles, so
`cycleMap_global_orientation` supplies one global orientation.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000 in
/-- A unique-neighbour rectangular block which intertwines two cycle
adjacency operators defines a locally cycle-intertwining selector. -/
theorem cycleSelector_neighborPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr3 : 3 ≤ r) (hn3 : 3 ≤ n)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (f : ZMod n → ZMod r)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hunique : ∀ x y, G.Adj (u x) (v y) ↔ x = f y) :
    ∀ y, ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1} := by
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x h ↦
    zmod_sub_one_ne_add_one_of_three_le hr3 x (huinj h)
  have hvpair : ∀ y, v (y - 1) ≠ v (y + 1) := fun y h ↦
    zmod_sub_one_ne_add_one_of_three_le hn3 y (hvinj h)
  have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D u v
    (1 : ZMod r) (1 : ZMod n) hcomm huD hvD hupair hvpair
  intro y
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hrec := hinter x y
  simp only [SimpleGraph.adjMatrix_apply, hunique] at hrec
  have hsub : x - 1 = f y ↔ x = f y + 1 := by
    constructor <;> intro h
    · calc x = (x - 1) + 1 := by ring
        _ = f y + 1 := by rw [h]
    · rw [h]
      ring
  have hadd : x + 1 = f y ↔ x = f y - 1 := by
    constructor <;> intro h
    · calc x = (x + 1) - 1 := by ring
        _ = f y - 1 := by rw [h]
    · rw [h]
      ring
  simp only [hsub, hadd] at hrec
  have hpm : f y - 1 ≠ f y + 1 :=
    zmod_sub_one_ne_add_one_of_three_le hr3 (f y)
  by_cases h₁ : x = f (y - 1) <;>
    by_cases h₂ : x = f (y + 1) <;>
    by_cases h₃ : x = f y - 1 <;>
    by_cases h₄ : x = f y + 1 <;>
    simp_all [eq_comm]

/-- **Graph-facing one-neighbour cover.**  If every vertex of the labeled
`e`-cycle has exactly one `G`-neighbour in the labeled `c`-cycle, that
neighbour is selected by a map which has one global cyclic orientation. -/
theorem exists_cycleCoverMap_global_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hone : ∀ y, (mixedAnchorSupport G (v y) u).card = 1) :
    ∃ f : ZMod n → ZMod r,
      (∀ x y, G.Adj (u x) (v y) ↔ x = f y) ∧
      ((∀ y, f (y + 1) = f y + 1) ∨
        (∀ y, f (y + 1) = f y - 1)) := by
  classical
  have hs : ∀ y, ∃! x, x ∈ mixedAnchorSupport G (v y) u := by
    intro y
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hone y)
    refine ⟨x, ?_, ?_⟩
    · rw [hx]
      simp
    · intro z hz
      rw [hx] at hz
      simpa using hz
  choose f hfmem hfun using hs
  refine ⟨f, ?_, ?_⟩
  · intro x y
    rw [G.adj_comm, ← mem_mixedAnchorSupport_iff]
    constructor
    · intro hx
      exact hfun y x hx
    · rintro rfl
      exact hfmem y
  · apply cycleMap_global_orientation hr f
    exact cycleSelector_neighborPair hr hn G D u v f huinj hvinj huD hvD hcomm
      (fun x y ↦ by
        rw [G.adj_comm, ← mem_mixedAnchorSupport_iff]
        exact ⟨fun hx ↦ hfun y x hx, fun h ↦ h ▸ hfmem y⟩)

end

end Erdos85
