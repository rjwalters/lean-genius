import Proofs.Erdos85SevenVertexSubcubicEquality

/-! A triangle exists in the seven-vertex nine-edge equality case. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The equality degree profile fixes the total second-order defect degree. -/
theorem sevenVertex_subcubic_nine_edges_sum_defect_degree
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9) :
    (∑ x : V, (secondOrderDefectGraph G).degree x) = 12 := by
  classical
  have hmin := sevenVertex_subcubic_nine_edges_degree_ge_two G hfree hcard hmax hedges
  have hcounts := sevenVertex_subcubic_nine_edges_degree_counts G hfree hcard hmax hedges
  have hconserve := sum_defectDegree_add_sum_weightedDegreeExcess_eq_card_mul_orderExcess
    G hfree (d := 2) (q := 4) (by omega) hmin (by omega)
  have heach : ∀ x, (G.degree x - 2) * (2 - 1) + G.degree x * (G.degree x - 2) =
      if G.degree x = 3 then 4 else 0 := by
    intro x
    have hcases : G.degree x = 2 ∨ G.degree x = 3 := by
      have := hmin x
      have := hmax x
      omega
    rcases hcases with h | h <;> simp [h]
  simp_rw [heach] at hconserve
  have hweight : (∑ x : V, if G.degree x = 3 then 4 else 0) = 16 := by
    rw [← Finset.sum_filter]
    simp [hcounts.2]
  rw [hweight, hcard] at hconserve
  omega

/-- Three distinct pairwise adjacent vertices exist; distinctness follows
from the loopless graph relation. No enumeration is used. -/
theorem sevenVertex_subcubic_nine_edges_exists_triangle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9) :
    ∃ x y z : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z x := by
  classical
  by_contra hn
  have hle : ∀ x, G.degree x ≤ (secondOrderDefectGraph G).degree x := by
    intro x
    have hsubset : G.neighborFinset x ⊆ triangleFreeNeighbors G x := by
      intro y hy
      have hxy : G.Adj x y := by simpa using hy
      apply (mem_triangleFreeNeighbors G x y).mpr
      refine ⟨hxy, ?_⟩
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hzx : G.Adj x z := by simpa using (Finset.mem_inter.mp hz).1
      have hzy : G.Adj y z := by simpa using (Finset.mem_inter.mp hz).2
      exact hn ⟨x, y, z, hxy, hzy, hzx.symm⟩
    have h1 := Finset.card_le_card hsubset
    have h2 : (triangleFreeNeighbors G x).card ≤ (secondOrderDefectGraph G).degree x := by
      rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
        secondOrderDefectGraph_neighborFinset]
      exact Finset.card_le_card Finset.subset_union_right
    rw [G.card_neighborFinset_eq_degree] at h1
    exact h1.trans h2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hle x)
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hdef := sevenVertex_subcubic_nine_edges_sum_defect_degree G hfree hcard hmax hedges
  rw [hedges] at hhand
  omega
end Erdos85
#print axioms Erdos85.sevenVertex_subcubic_nine_edges_sum_defect_degree
#print axioms Erdos85.sevenVertex_subcubic_nine_edges_exists_triangle
