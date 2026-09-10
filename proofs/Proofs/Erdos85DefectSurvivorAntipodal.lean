import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85SquareOrderLowTriangleDefectIdentity

/-! Identifying the vertices left by defect-neighborhood isolation with
antipodal misses, and transporting the existing square-order triangle ledger. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The surviving defect neighbors are exactly the antipodal vertices. -/
theorem defect_neighbor_sdiff_eq_antipodal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v : V) :
    (secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v =
      antipodalNeighbors G v := by
  ext x
  simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
    mem_antipodalNeighbors]
  constructor
  · rintro ⟨hdef, hnot⟩
    exact ⟨hdef.ne.symm, hnot,
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree hdef.ne).mp hdef⟩
  · rintro ⟨hne, hnot, hzero⟩
    exact ⟨(secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree hne.symm).mpr hzero,
      hnot⟩

/-- The existing square-order local triangle identity counts precisely the
survivors used in the sparse overlap bound. -/
theorem squareOrder_low_survivors_add_highIncidence_add_one_eq_two_mul_localEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V} (hx : G.degree x = d) :
    ((secondOrderDefectGraph G).neighborFinset x \ G.neighborFinset x).card +
      squareOrderHighIncidenceCount G d x + 1 =
      2 * (G.induce (G.neighborSet x)).edgeFinset.card := by
  rw [defect_neighbor_sdiff_eq_antipodal G hfree x]
  exact squareOrder_low_antipodal_add_highIncidence_add_one_eq_two_mul_localEdges
    G hfree hd hmin hcover hcard hx
end Erdos85
