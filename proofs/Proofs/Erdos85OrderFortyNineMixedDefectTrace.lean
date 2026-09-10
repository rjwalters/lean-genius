import Proofs.Erdos85NonregularFifthMoment
import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85DegreeExcessStratification
import Proofs.Erdos85OrderFortyNineWeightedDefectDegree
import Proofs.Erdos85MixedFifthTraceResidue
import Proofs.Erdos85OrderFortyNineHighPartnerBound

/-! Graph-side mixed traces for the nonregular order49 fifth moment. -/
namespace Erdos85
open SimpleGraph Matrix Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The nonregular cubic relation retains the full degree sum. -/
theorem c4Free_trace_cube_add_adj_defect_eq_degree_sum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    Matrix.trace (G.adjMatrix ℤ ^ 3) +
      Matrix.trace (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ) =
      ∑ v, (G.degree v : ℤ) := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let K := degreePredDiagonal G
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hsq : A * A = K + J - D :=
    adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect G hfree
  have hcube : A ^ 3 = A * K + A * J - A * D := by
    rw [show A ^ 3 = A * (A * A) by noncomm_ring, hsq]
    noncomm_ring
  have hAK : Matrix.trace (A * K) = 0 := by
    simp [Matrix.trace, Matrix.diag, K, degreePredDiagonal, Matrix.mul_diagonal,
      A, SimpleGraph.adjMatrix_apply]
  have hAJ : Matrix.trace (A * J) = ∑ v, (G.degree v : ℤ) := by
    simp only [Matrix.trace, Matrix.diag, A, J,
      adjMatrix_mul_onesMatrix_apply_eq_degree]
  change Matrix.trace (A ^ 3) + Matrix.trace (A * D) = _
  rw [hcube, Matrix.trace_sub, Matrix.trace_add, hAK, hAJ]
  ring

/-- Defect edges are supported on degree7 vertices, so the degree correction
in the mixed trace is exactly6 even though the original graph is nonregular. -/
theorem orderFortyNine_trace_adj_degreePred_defect_eq_six
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49) :
    Matrix.trace (G.adjMatrix ℤ * degreePredDiagonal G *
      (secondOrderDefectGraph G).adjMatrix ℤ) =
      6 * Matrix.trace (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ) := by
  classical
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  have hpoint (i j : V) :
      A i j * ((G.degree j : ℤ) - 1) * D j i = 6 * (A i j * D j i) := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard j with hj | hj
    · norm_num [hj]
      ring
    · have hz := (squareOrder_degree_succ_highRoot_structure G hfree
        (d := 7) (by norm_num) hmin (by simpa using hcard) hj).1
      have hn : ¬ (secondOrderDefectGraph G).Adj j i := by
        intro ha
        have hp : 0 < ((secondOrderDefectGraph G).neighborFinset j).card :=
          Finset.card_pos.mpr ⟨i, ((secondOrderDefectGraph G).mem_neighborFinset j i).mpr ha⟩
        rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hz] at hp
        omega
      simp [D, SimpleGraph.adjMatrix_apply, hn]
  change Matrix.trace (A * degreePredDiagonal G * D) = 6 * Matrix.trace (A * D)
  simp only [Matrix.trace, Matrix.diag, degreePredDiagonal]
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (A * degreePredDiagonal G) i j * D j i = _
  rw [degreePredDiagonal, Matrix.mul_diagonal]
  exact hpoint i j
/-- All degree and mixed-weight ledgers are discharged from actual graph
hypotheses. Translation of the cubic trace into a chosen triangle census is
left to the caller. -/
theorem orderFortyNine_fifth_trace_eq_cubic_and_overlap
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    Matrix.trace (A ^ 5) = 12691 +
      261 * ((squareOrderHighVertices G 7).card : ℤ) +
      12 * Matrix.trace (A ^ 3) + Matrix.trace (A * D * D) := by
  have hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7 := by
    intro u v huv
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin hcard u with hu | hu
    · exact Or.inl hu
    · exact Or.inr (orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin hcard hu huv)
  have hb := c4Free_nonregular_fifth_trace_degree_expansion G hfree
  dsimp only at hb ⊢
  rw [hcard,
    orderFortyNine_sum_degree_eq_cube_add_high G hfree hmin hcover hcard,
    orderFortyNine_sum_degree_mul_pred G hfree hmin hcover hcard,
    orderFortyNine_sum_degree_mul_defectDegree G hfree hmin hcover hcard,
    orderFortyNine_trace_adj_degreePred_defect_eq_six G hfree hmin hcard] at hb
  have hc := c4Free_trace_cube_add_adj_defect_eq_degree_sum G hfree
  rw [orderFortyNine_sum_degree_eq_cube_add_high G hfree hmin hcover hcard] at hc
  push_cast at hb
  linear_combination hb - 12 * hc
/-- The q7 overlap residue now needs only the cubic/triangle conversion;
all fifth-trace and degree ledgers follow from actual graph hypotheses. -/
theorem orderFortyNine_overlap_residue_of_cubic_trace
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49) (T : ℤ)
    (htri : Matrix.trace (G.adjMatrix ℤ ^ 3) =
      6*T + 24*((squareOrderHighVertices G 7).card : ℤ)) :
    Int.ModEq 5
      (Matrix.trace (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ))
      (3*T + ((squareOrderHighVertices G 7).card : ℤ) + 4) := by
  apply mixed_defect_trace_residue_of_fifth_identity (G.adjMatrix ℤ)
    (SimpleGraph.trace_adjMatrix ℤ G)
  have hb := orderFortyNine_fifth_trace_eq_cubic_and_overlap G hfree hmin hcard
  dsimp only at hb
  rw [hb, htri]
  ring
/-- Incidence-sum version for the local graph ledger, avoiding any choice
of global triangle objects. The cubic conversion is the sole extra premise. -/
theorem orderFortyNine_overlap_residue_of_cubic_incidence
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hcard : Fintype.card V = 49) (S : ℤ)
    (htri : Matrix.trace (G.adjMatrix ℤ ^ 3) =
      2*S + 24*((squareOrderHighVertices G 7).card : ℤ)) :
    Int.ModEq 5
      (Matrix.trace (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ))
      (S + ((squareOrderHighVertices G 7).card : ℤ) + 4) := by
  obtain ⟨k, hk⟩ := five_dvd_trace_fifth_of_trace_zero (G.adjMatrix ℤ)
    (SimpleGraph.trace_adjMatrix ℤ G)
  have hb := orderFortyNine_fifth_trace_eq_cubic_and_overlap G hfree hmin hcard
  dsimp only at hb
  rw [hb, htri] at hk
  change _ % 5 = _ % 5
  omega
end Erdos85
