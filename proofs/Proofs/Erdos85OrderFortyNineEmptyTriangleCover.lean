import Proofs.Erdos85IndependentTriangleCover
import Proofs.Erdos85OrderFortyNineLowTriangles
import Proofs.Erdos85OrderFortyNineHighIncidenceCensus

/-!
# Actual empty-support triangle covers at order49

The existing all-low triangle-existence theorem gives a three-clique in
the induced low graph through every empty-support vertex. This removes
the separate triangle-cover premise from the generic counting bounds.
-/

namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

/-- Every actual empty-support low vertex belongs to a triangle in the
induced low graph. -/
theorem orderFortyNine_empty_low_vertex_mem_triangle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (x : (↑(orderFortyNineLowVertices G) : Set V))
    (hempty : (G.neighborFinset x.val ∩ orderFortyNineHighVertices G).card = 0) :
    ∃ t ∈ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3,
      x ∈ t := by
  classical
  have hxnot := (Finset.mem_sdiff.mp x.property).2
  have hx7 : G.degree x.val = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard x.val with h7 | h8
    · exact h7
    · exact False.elim (hxnot (by simp [orderFortyNineHighVertices, h8]))
  obtain ⟨y, z, hy, hz, hxy, hxz, hyz⟩ :=
    orderFortyNine_exists_allLow_triangle_of_highNeighborCount_zero
      G hfree hmin hcard hx7 hempty
  have hyLow : y ∈ orderFortyNineLowVertices G := by
    simp [orderFortyNineLowVertices, orderFortyNineHighVertices, hy]
  have hzLow : z ∈ orderFortyNineLowVertices G := by
    simp [orderFortyNineLowVertices, orderFortyNineHighVertices, hz]
  let y' : (↑(orderFortyNineLowVertices G) : Set V) := ⟨y, hyLow⟩
  let z' : (↑(orderFortyNineLowVertices G) : Set V) := ⟨z, hzLow⟩
  refine ⟨{x, y', z'}, ?_, by simp⟩
  apply SimpleGraph.mem_cliqueFinset_iff.mpr
  apply SimpleGraph.is3Clique_triple_iff.mpr
  exact ⟨hxy, hxz, hyz⟩

/-- Independent actual empty-support vertices require distinct additional
low triangles beyond a known family that avoids them. -/
theorem orderFortyNine_empty_independent_triangle_cover_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (S : Finset (↑(orderFortyNineLowVertices G) : Set V))
    (known : Finset (Finset (↑(orderFortyNineLowVertices G) : Set V)))
    (hempty : ∀ x ∈ S,
      (G.neighborFinset x.val ∩ orderFortyNineHighVertices G).card = 0)
    (hind : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u.val v.val)
    (hknown : known ⊆ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3)
    (havoid : ∀ t ∈ known, Disjoint S t) :
    known.card + S.card ≤
      ((G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3).card := by
  classical
  exact independent_triangle_cover_bound
    (G.induce (↑(orderFortyNineLowVertices G) : Set V)) S known hind
    (fun x hx => orderFortyNine_empty_low_vertex_mem_triangle
      G hfree hmin hcard x (hempty x hx)) hknown havoid

/-- General actual empty-support vertices require at least one additional
low triangle per three vertices outside the known triangle family. -/
theorem orderFortyNine_empty_triangle_cover_card_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (S : Finset (↑(orderFortyNineLowVertices G) : Set V))
    (known : Finset (Finset (↑(orderFortyNineLowVertices G) : Set V)))
    (hempty : ∀ x ∈ S,
      (G.neighborFinset x.val ∩ orderFortyNineHighVertices G).card = 0)
    (hknown : known ⊆ (G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3)
    (havoid : ∀ t ∈ known, Disjoint S t) :
    S.card ≤ 3 *
      (((G.induce (↑(orderFortyNineLowVertices G) : Set V)).cliqueFinset 3).card - known.card) := by
  classical
  exact triangle_cover_card_bound
    (G.induce (↑(orderFortyNineLowVertices G) : Set V)) S known
    (fun x hx => orderFortyNine_empty_low_vertex_mem_triangle
      G hfree hmin hcard x (hempty x hx)) hknown havoid

end
end Erdos85

#print axioms Erdos85.orderFortyNine_empty_low_vertex_mem_triangle
#print axioms Erdos85.orderFortyNine_empty_independent_triangle_cover_bound
#print axioms Erdos85.orderFortyNine_empty_triangle_cover_card_bound
