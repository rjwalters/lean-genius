import Proofs.Erdos85OrderFortyNineLowNeighborhoodPartition

/-!
# Required high-color neighbors have compatible empty neighborhoods

The singleton-resolution computations reject a required adjacency when an
edge between the two empty neighborhoods would close a four-cycle.  Here
that obstruction and the existence of a compatible neighbor for each high
vertex are proved directly for the actual graph.  Exclusion of special
vertices remains an explicit premise; no finite enumeration is certified.
-/

namespace Erdos85
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacent vertices outside E cannot have an edge crossing their
neighborhoods in E: its four endpoints would form a C4. -/
theorem adjacent_outside_empty_neighborhoods_compatible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (E : Finset V)
    {x y : V} (hx : x ∉ E) (hy : y ∉ E) (hxy : G.Adj x y) :
    ∀ a ∈ E, ∀ b ∈ E, G.Adj x a → G.Adj y b → ¬ G.Adj a b := by
  intro a ha b hb hxa hyb hab
  have hxb : x ≠ b := by
    intro h
    exact hx (h ▸ hb)
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree x b hxb
  have haCommon : a ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxa, hab.symm⟩
  have hyCommon : y ∈ G.neighborFinset x ∩ G.neighborFinset b := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy, hyb.symm⟩
  have hay : a = y := Finset.card_le_one.mp hc a haCommon y hyCommon
  exact hy (hay ▸ ha)

/-- Every low root outside E has a compatible low neighbor of each high
color, outside any explicitly forbidden set of its nonneighbors.

For H3 ordinary singletons, E is the empty-support class and the forbidden
set consists of the triple-support and special singleton vertices.  The
assertion that those vertices are nonneighbors is deliberately explicit. -/
theorem orderFortyNine_exists_compatible_high_color_neighbor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ v : V, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49)
    (E forbidden : Finset V)
    (hE : ∀ v ∈ E,
      (G.neighborFinset v ∩ orderFortyNineHighVertices G).card = 0)
    {x h : V} (hx7 : G.degree x = 7) (hxE : x ∉ E)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hforbidden : ∀ z ∈ forbidden, ¬ G.Adj x z) :
    ∃ y, y ≠ x ∧ G.degree y = 7 ∧ y ∉ E ∧ y ∉ forbidden ∧
      G.Adj x y ∧ G.Adj y h ∧
      ∀ a ∈ E, ∀ b ∈ E, G.Adj x a → G.Adj y b → ¬ G.Adj a b := by
  obtain ⟨y, hy, _⟩ := orderFortyNine_low_neighborhood_partitions_highs
    G hfree hmin hcard hx7 hh
  have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy.1
  have hyE : y ∉ E := by
    intro he
    have hempty := Finset.card_eq_zero.mp (hE y he)
    have hmem : h ∈ G.neighborFinset y ∩ orderFortyNineHighVertices G := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y h).mpr hy.2, hh⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hh8 : G.degree h = 8 := (Finset.mem_filter.mp hh).2
  have hy7 : G.degree y = 7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
    G hfree hmin hcard hh8 hy.2.symm
  refine ⟨y, hxy.ne.symm, hy7, hyE, ?_, hxy, hy.2, ?_⟩
  · intro hf
    exact hforbidden y hf hxy
  · exact adjacent_outside_empty_neighborhoods_compatible G hfree E hxE hyE hxy

end Erdos85

#print axioms Erdos85.adjacent_outside_empty_neighborhoods_compatible
#print axioms Erdos85.orderFortyNine_exists_compatible_high_color_neighbor
