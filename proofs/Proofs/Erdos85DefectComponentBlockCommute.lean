import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85FrequencyPairTransport

/-! # Commutation on a defect-component block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If an ambient adjacency matrix commutes with the adjacency matrix of a
second graph, then the two diagonal blocks on any connected component of the
second graph commute.  The ambient graph may still have edges leaving the
component: only the second matrix needs to be block diagonal. -/
theorem induce_component_adjMatrix_comm_of_comm
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hcomm : G.adjMatrix K * D.adjMatrix K =
      D.adjMatrix K * G.adjMatrix K)
    (c : D.ConnectedComponent) :
    (G.induce c.supp).adjMatrix K * (D.induce c.supp).adjMatrix K =
      (D.induce c.supp).adjMatrix K * (G.induce c.supp).adjMatrix K := by
  classical
  let p : V → Prop := fun x ↦ x ∈ c.supp
  have hDoutIn : (D.adjMatrix K).toBlock (fun x ↦ ¬p x) p = 0 := by
    ext i j
    simp only [Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply,
      Matrix.zero_apply]
    rw [if_neg]
    intro hij
    exact i.2 ((c.mem_supp_congr_adj hij).mpr j.2)
  have hDinOut : (D.adjMatrix K).toBlock p (fun x ↦ ¬p x) = 0 := by
    ext i j
    simp only [Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply,
      Matrix.zero_apply]
    rw [if_neg]
    intro hij
    exact j.2 ((c.mem_supp_congr_adj hij).mp i.2)
  have hblock := congrArg (fun M ↦ M.toBlock p p) hcomm
  rw [Matrix.toBlock_mul_eq_add p p p (G.adjMatrix K) (D.adjMatrix K),
    Matrix.toBlock_mul_eq_add p p p (D.adjMatrix K) (G.adjMatrix K),
    hDoutIn, hDinOut, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    add_zero] at hblock
  have hGblock : (G.adjMatrix K).toBlock p p =
      (G.induce c.supp).adjMatrix K := by
    ext i j
    simp [p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hDblock : (D.adjMatrix K).toBlock p p =
      (D.induce c.supp).adjMatrix K := by
    ext i j
    simp [p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  rw [hGblock, hDblock] at hblock
  exact hblock

/-- In a regular `C₄`-free graph, ambient adjacency and defect adjacency
commute after restriction to every individual defect component. -/
theorem adjMatrix_comm_secondOrderDefect_induce_component_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (G.induce c.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ =
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
        (G.induce c.supp).adjMatrix ℤ := by
  exact induce_component_adjMatrix_comm_of_comm G (secondOrderDefectGraph G)
    (adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg) c

/-- Complex form of component-block commutation, ready for Hermitian spectral
arguments on a distinguished defect component. -/
theorem adjMatrix_comm_secondOrderDefect_induce_component_of_regular_complex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (G.induce c.supp).adjMatrix ℂ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ =
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ *
        (G.induce c.supp).adjMatrix ℂ := by
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hcommC : G.adjMatrix ℂ * (secondOrderDefectGraph G).adjMatrix ℂ =
      (secondOrderDefectGraph G).adjMatrix ℂ * G.adjMatrix ℂ := by
    have h := congrArg (fun A ↦ A.map (Int.castRingHom ℂ)) hcommZ
    simpa only [Matrix.map_mul, adjMatrix_map_intCast] using h
  exact induce_component_adjMatrix_comm_of_comm G (secondOrderDefectGraph G)
    hcommC c

end

end Erdos85
