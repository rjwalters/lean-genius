import Proofs.Erdos85OrderSixtyFourRegularKernel
import Proofs.Erdos85OrderSixtyFourSevenComponent
import Proofs.Erdos85OrderSixtyFourResidualLaplacianProduct
import Proofs.Erdos85TriangleFreeCommutatorGap

/-! # The exact second moment of the distinguished defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Complex-valued form of the adjacency-square degree-sum identity. -/
theorem trace_adjMatrix_sq_complex_eq_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Matrix.trace (H.adjMatrix ℂ * H.adjMatrix ℂ) =
      ∑ x : V, (H.degree x : ℂ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply]
  rw [H.adjMatrix_mul_self_apply_self]

/-- In the seven-component order-64 branch, the distinguished order-16
defect block is seven-regular.  Its adjacency-square trace is therefore
`16 * 7 = 112`; after removing the principal eigenvalue `7`, the exact
nonprincipal square-moment budget is `63`. -/
theorem orderSixtyFour_seven_defect_components_defect_secondMoment
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      Matrix.trace
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ) = 112 ∧
      Matrix.trace
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ) - 7 ^ 2 = 63 ∧
      Matrix.trace
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ) = 112 ∧
      (Matrix.trace
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ)).re - 7 ^ 2 = 63 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have hregD : ∀ x : Fin 64, D.degree x = 7 :=
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
  have hregH : ∀ x : c.supp, (D.induce c.supp).degree x = 7 := by
    intro x
    rw [degree_induce_connectedComponent_supp_explicit D c x, hregD]
  have hcard : Fintype.card c.supp = 16 := by
    have hs : Fintype.card c.supp = c.supp.ncard := by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
    rw [hs, hc16]
  have htrace : Matrix.trace
      ((D.induce c.supp).adjMatrix ℤ *
      (D.induce c.supp).adjMatrix ℤ) = 112 := by
    rw [trace_adjMatrix_sq_eq_sum_degrees]
    simp [hregH, hcard]
  have htraceC : Matrix.trace
      ((D.induce c.supp).adjMatrix ℂ *
      (D.induce c.supp).adjMatrix ℂ) = 112 := by
    rw [trace_adjMatrix_sq_complex_eq_sum_degrees]
    simp [hregH, hcard]
    norm_num
  refine ⟨c, hc16, htrace, ?_, htraceC, ?_⟩
  · rw [htrace]
    norm_num
  · rw [htraceC]
    norm_num

end

end Erdos85
