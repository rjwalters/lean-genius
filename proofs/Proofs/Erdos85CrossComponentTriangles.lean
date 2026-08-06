import Proofs.Erdos85CycleCoverGraph

/-!
# Triangles on edges between defect components

The component quotient remembers how many original-graph edges run between
second-order defect components, but forgets the triangles containing those
edges.  This file records the first genuinely geometric constraint on such
blocks: every cross-component edge lies in a unique triangle.  Moreover, if
the reverse quotient entry is one, the third vertex cannot return to the
source component.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- An edge of `G` joining distinct connected components of the second-order
defect graph has exactly one common neighbor.  Equivalently, every such edge
lies in a unique triangle. -/
theorem existsUnique_commonNeighbor_of_crossComponent_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    {x y : V} (hx : x ∈ c.supp) (hy : y ∈ e.supp) (hxy : G.Adj x y) :
    ∃! z : V, G.Adj x z ∧ G.Adj y z := by
  let D := secondOrderDefectGraph G
  have hxc : D.connectedComponentMk x = c :=
    (ConnectedComponent.mem_supp_iff c x).mp hx
  have hye : D.connectedComponentMk y = e :=
    (ConnectedComponent.mem_supp_iff e y).mp hy
  have hnotD : y ∉ D.neighborFinset x := by
    intro hmem
    have hadjD : D.Adj x y := (D.mem_neighborFinset x y).mp hmem
    have hm := ConnectedComponent.connectedComponentMk_eq_of_adj hadjD
    apply hce
    rw [← hxc, ← hye]
    exact hm
  have hne : x ≠ y := G.ne_of_adj hxy
  have hone : (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
    rw [card_common_eq_if_secondOrderDefect_of_even G hfree hd heven hmin
      hcard x y hne, if_neg hnotD]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
  refine ⟨z, ?_, ?_⟩
  · have : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by simp [hz]
    simpa only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] using this
  · intro w hw
    have hwmem : w ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      simpa only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] using hw
    rw [hz] at hwmem
    simpa using hwmem

/-- If a target vertex has a unique neighbor in a source defect component,
then the third vertex of the unique triangle on that cross-component edge
lies outside the source component. -/
theorem commonNeighbor_not_mem_source_of_unique_componentNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : SimpleGraph V}
    (c : D.ConnectedComponent) {x y z : V}
    (hunique : ∀ w : V, w ∈ c.supp → G.Adj w y → w = x)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    z ∉ c.supp := by
  intro hz
  have hzx : z = x := hunique z hz hyz.symm
  subst z
  exact G.loopless.irrefl x hxz

/-- Graph-of-a-selector form used by cyclic covers: the unique triangle on
each selected cross edge has its third vertex outside the selector's source
component.  This is information not visible in the component quotient. -/
theorem existsUnique_commonNeighbor_outside_source_of_cycleSelector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (u : ZMod r → V) (v : ZMod n → V)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (f : ZMod n → ZMod r)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (y : ZMod n) :
    ∃! z : V,
      (G.Adj (u (f y)) z ∧ G.Adj (v y) z) ∧ z ∉ c.supp := by
  have hux : u (f y) ∈ c.supp := by
    rw [← huRange]
    exact ⟨f y, rfl⟩
  have hvy : v y ∈ e.supp := by
    rw [← hvRange]
    exact ⟨y, rfl⟩
  have hcross : G.Adj (u (f y)) (v y) := (hadj (f y) y).mpr rfl
  obtain ⟨z, hz, hzunique⟩ :=
    existsUnique_commonNeighbor_of_crossComponent_adj G hfree hd heven hmin
      hcard c e hce hux hvy hcross
  have huniqueSource : ∀ w : V, w ∈ c.supp → G.Adj w (v y) → w = u (f y) := by
    intro w hw hwv
    rw [← huRange] at hw
    obtain ⟨x, rfl⟩ := hw
    exact congrArg u ((hadj x y).mp hwv)
  have hzout : z ∉ c.supp :=
    commonNeighbor_not_mem_source_of_unique_componentNeighbor G c
      huniqueSource hz.1 hz.2
  refine ⟨z, ⟨hz, hzout⟩, ?_⟩
  intro w hw
  exact hzunique w hw.1

end

end Erdos85
