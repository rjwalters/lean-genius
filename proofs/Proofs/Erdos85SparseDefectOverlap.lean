import Proofs.Erdos85DefectNeighborhoodIsolation
import Proofs.Erdos85RootedFifthWalkDefectNeighborhood

/-! Aggregate graph overlap when all but one defect neighborhood have at most
one vertex left after removing original neighbors. This is a conditional graph
step toward q7 triangle-count cuts; the q7 census and Newton congruence are
not supplied as conclusions of this file. -/
namespace Erdos85
open SimpleGraph Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only the exceptional root contributes to the mixed trace. -/
theorem sparse_defect_overlap_trace_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (e : V)
    (hsparse : ∀ v, v ≠ e →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1) :
    Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) =
      2 * ((G.induce (↑((secondOrderDefectGraph G).neighborFinset e) : Set V)).edgeFinset.card : ℤ) := by
  classical
  rw [Matrix.trace, Finset.sum_eq_single e]
  · exact defect_adj_defect_diagonal_eq_two_mul_induced_edges G (secondOrderDefectGraph G) e
  · intro v _ hve
    simp only [Matrix.diag]
    rw [defect_adj_defect_diagonal_eq_two_mul_induced_edges,
      defect_neighborhood_edges_eq_zero_of_surviving_le_one G hfree v (hsparse v hve)]
    norm_num
  · simp

/-- With at most two survivors at the exceptional root, the trace is at most2. -/
theorem sparse_defect_overlap_trace_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (e : V)
    (hsparse : ∀ v, v ≠ e →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1)
    (he : ((secondOrderDefectGraph G).neighborFinset e \ G.neighborFinset e).card ≤ 2) :
    Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) ≤ 2 := by
  rw [sparse_defect_overlap_trace_eq G hfree e hsparse]
  have h := defect_neighborhood_edges_le_one_of_surviving_le_two G hfree e he
  omega

/-- The sparse overlap cannot have residue1 modulo5. -/
theorem sparse_defect_overlap_trace_not_mod_five_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (e : V)
    (hsparse : ∀ v, v ≠ e →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1)
    (he : ((secondOrderDefectGraph G).neighborFinset e \ G.neighborFinset e).card ≤ 2) :
    ¬ Int.ModEq 5 (Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ)) 1 := by
  rw [sparse_defect_overlap_trace_eq G hfree e hsparse]
  have h := defect_neighborhood_edges_le_one_of_surviving_le_two G hfree e he
  have cases := Nat.le_one_iff_eq_zero_or_eq_one.mp h
  rcases cases with hz | ho
  · rw [hz]
    norm_num [Int.ModEq]
  · rw [ho]
    norm_num [Int.ModEq]
end Erdos85
