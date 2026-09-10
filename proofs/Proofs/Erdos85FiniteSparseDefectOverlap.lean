import Proofs.Erdos85DefectNeighborhoodIsolation
import Proofs.Erdos85RootedFifthWalkDefectNeighborhood

/-! Finite exceptional-set defect-overlap bound. The q7 census, triangle
count, and Newton congruence must still be supplied to apply this graph step. -/
namespace Erdos85
open SimpleGraph Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only exceptional roots contribute to the trace. -/
theorem finite_sparse_defect_overlap_trace_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (E : Finset V)
    (hsparse : ∀ v, v ∉ E →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1) :
    Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) =
      2 * ∑ v ∈ E,
        ((G.induce (↑((secondOrderDefectGraph G).neighborFinset v) : Set V)).edgeFinset.card : ℤ) := by
  classical
  rw [Matrix.trace]
  change (∑ v : V, _) = _
  rw [Finset.mul_sum]
  calc
    _ = ∑ v ∈ E, (((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) v v) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ E)
      intro v _ hv
      rw [defect_adj_defect_diagonal_eq_two_mul_induced_edges,
        defect_neighborhood_edges_eq_zero_of_surviving_le_one G hfree v (hsparse v hv)]
      norm_num
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      exact defect_adj_defect_diagonal_eq_two_mul_induced_edges G (secondOrderDefectGraph G) v

/-- At most two survivors per exceptional root bound the mixed trace by twice
its exceptional-set cardinality. -/
theorem finite_sparse_defect_overlap_trace_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (E : Finset V)
    (hsparse : ∀ v, v ∉ E →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1)
    (hexception : ∀ v ∈ E,
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 2) :
    Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) ≤ 2 * (E.card : ℤ) := by
  rw [finite_sparse_defect_overlap_trace_eq G hfree E hsparse]
  have hsum : (∑ v ∈ E,
      ((G.induce (↑((secondOrderDefectGraph G).neighborFinset v) : Set V)).edgeFinset.card : ℤ)) ≤
      (E.card : ℤ) := by
    calc
      _ ≤ ∑ _v ∈ E, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast defect_neighborhood_edges_le_one_of_surviving_le_two G hfree v
          (hexception v hv)
      _ = _ := by simp
  omega

/-- Up to two exceptional roots rule out residue one modulo five. -/
theorem finite_sparse_defect_overlap_trace_not_mod_five_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (E : Finset V)
    (hsparse : ∀ v, v ∉ E →
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1)
    (hexception : ∀ v ∈ E,
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 2)
    (hcard : E.card ≤ 2) :
    ¬ Int.ModEq 5 (Matrix.trace ((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ)) 1 := by
  have hle := finite_sparse_defect_overlap_trace_le G hfree E hsparse hexception
  rw [finite_sparse_defect_overlap_trace_eq G hfree E hsparse] at hle ⊢
  have hnonneg : 0 ≤ ∑ v ∈ E,
      ((G.induce (↑((secondOrderDefectGraph G).neighborFinset v) : Set V)).edgeFinset.card : ℤ) := by
    positivity
  intro hmod
  change _ % 5 = 1 % 5 at hmod
  omega
end Erdos85
