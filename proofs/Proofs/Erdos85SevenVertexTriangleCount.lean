import Proofs.Erdos85SevenVertexSubcubicTriangle
import Proofs.Erdos85ClosedNeighborhoodEnergyStrictResidue

/-! Formal triangle counts in the seven-vertex subcubic equality case. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a subcubic C4-free graph, a vertex belongs to at most one triangle. -/
theorem subcubic_c4Free_local_triangle_count_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmax : ∀ x, G.degree x ≤ 3) (x : V) :
    (G.induce (G.neighborSet x)).edgeFinset.card ≤ 1 := by
  have h := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have := hmax x
  omega

/-- The triangle count of a subcubic C4-free graph is at most one third
of its vertex count. -/
theorem subcubic_c4Free_three_mul_triangle_count_le_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmax : ∀ x, G.degree x ≤ 3) :
    3 * (G.cliqueFinset 3).card ≤ Fintype.card V := by
  rw [← sum_localEdges_eq_three_mul_cliques G]
  calc
    _ ≤ ∑ _x : V, 1 := Finset.sum_le_sum (fun x _ =>
      subcubic_c4Free_local_triangle_count_le_one G hfree hmax x)
    _ = _ := by simp

/-- Exactly one or two triangles occur at the nine-edge equality endpoint. -/
theorem sevenVertex_subcubic_nine_edges_triangle_count_one_or_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9) :
    (G.cliqueFinset 3).card = 1 ∨ (G.cliqueFinset 3).card = 2 := by
  classical
  have hupper := subcubic_c4Free_three_mul_triangle_count_le_order G hfree hmax
  obtain ⟨x, y, z, hxy, hyz, hzx⟩ :=
    sevenVertex_subcubic_nine_edges_exists_triangle G hfree hcard hmax hedges
  have htriangle : G.IsNClique 3 {x, y, z} := by
    rw [SimpleGraph.is3Clique_iff]
    exact ⟨x, y, z, hxy, hzx.symm, hyz, rfl⟩
  have hpos : 0 < (G.cliqueFinset 3).card := Finset.card_pos.mpr
    ⟨{x, y, z}, G.mem_cliqueFinset_iff.mpr htriangle⟩
  omega
end Erdos85
#print axioms Erdos85.subcubic_c4Free_local_triangle_count_le_one
#print axioms Erdos85.subcubic_c4Free_three_mul_triangle_count_le_order
#print axioms Erdos85.sevenVertex_subcubic_nine_edges_triangle_count_one_or_two
